/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons077
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10920 (p : Pattern) (guard : d1964 p = 1) : d700 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10908 p hg
    simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10919 p hg
    simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10921 (p : Pattern) (guard : d1965 p = 1) : d700 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10901 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10920 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10922 (p : Pattern) (guard : d1943 p = 1) : d5 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d1943, d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d1943, d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10923 (p : Pattern) (guard : d1947 p = 1) : d5 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10922 p hg
    simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9533 p hg
    simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10924 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9415 p hg
    simpa only [d1293, d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10925 (p : Pattern) (guard : d1951 p = 1) : d37 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10924 p hg
    simpa only [d1951, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10926 (p : Pattern) (guard : d1952 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10923 p hg
    simpa only [d1952, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10925 p hg
    simpa only [d1952, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10927 (p : Pattern) (guard : d1953 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10905 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10926 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10928 (p : Pattern) (guard : d1958 p = 1) : d700 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10927 p hg
    simpa only [d1958, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d1958, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10929 (p : Pattern) (guard : d1963 p = 1) : d700 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10928 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10918 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10930 (p : Pattern) (guard : d1951 p = 1) : d5 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10924 p hg
    simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10931 (p : Pattern) (guard : d1956 p = 1) : d697 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10930 p hg
    simpa only [d1956, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2375 p hg
    simpa only [d1956, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10932 (p : Pattern) (guard : d1957 p = 1) : d697 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10910 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10931 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10933 (p : Pattern) (guard : d1962 p = 1) : d700 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10932 p hg
    simpa only [d1962, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10917 p hg
    simpa only [d1962, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10934 (p : Pattern) (guard : d0 p = 1) : d697 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10935 (p : Pattern) (guard : d1961 p = 1) : d697 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10914 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10934 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10936 (p : Pattern) (guard : d1966 p = 1) : d700 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10935 p hg
    simpa only [d1966, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1966, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10937 (p : Pattern) (guard : d1967 p = 1) : d700 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10933 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10936 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10938 (p : Pattern) (guard : d1968 p = 1) : d700 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10929 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10937 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10939 (p : Pattern) (guard : d1969 p = 1) : d700 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10920 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10938 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10940 (p : Pattern) (guard : d1970 p = 1) : d700 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10921 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10939 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10941 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare699 p hg
    simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10942 (p : Pattern) (guard : d1944 p = 1) : d11 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10941 p hg
    simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10943 (p : Pattern) (guard : d1948 p = 1) : d698 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10942 p hg
    simpa only [d1948, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10875 p hg
    simpa only [d1948, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10944 (p : Pattern) (guard : d1949 p = 1) : d699 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10888 p hg
    simpa only [d1949, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10943 p hg
    simpa only [d1949, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10945 (p : Pattern) (guard : d1954 p = 1) : d699 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10944 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10884 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10946 (p : Pattern) (guard : d1958 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10884 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10947 (p : Pattern) (guard : d1959 p = 1) : d699 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10945 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10946 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10948 (p : Pattern) (guard : d1962 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10917 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10949 (p : Pattern) (guard : d1963 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10946 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10948 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10950 (p : Pattern) (guard : d1964 p = 1) : d699 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10947 p hg
    simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10949 p hg
    simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10951 (p : Pattern) (guard : d1943 p = 1) : d11 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare699 p hg
    simpa only [d1943, d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d1943, d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10952 (p : Pattern) (guard : d1947 p = 1) : d11 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10951 p hg
    simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9514 p hg
    simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10953 (p : Pattern) (guard : d1952 p = 1) : d698 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10952 p hg
    simpa only [d1952, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9617 p hg
    simpa only [d1952, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10954 (p : Pattern) (guard : d1953 p = 1) : d699 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10890 p hg
    simpa only [d1953, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10953 p hg
    simpa only [d1953, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10955 (p : Pattern) (guard : d1958 p = 1) : d699 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10954 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10956 (p : Pattern) (guard : d1963 p = 1) : d699 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10955 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10948 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10957 (p : Pattern) (guard : d1966 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10917 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10958 (p : Pattern) (guard : d1967 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10948 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10957 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10959 (p : Pattern) (guard : d1968 p = 1) : d699 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10956 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10958 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10960 (p : Pattern) (guard : d1969 p = 1) : d699 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10950 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10959 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10961 (p : Pattern) (guard : d1957 p = 1) : d701 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10894 p hg
    simpa only [d1957, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10962 (p : Pattern) (guard : d1958 p = 1) : d702 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10954 p hg
    simpa only [d1958, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10961 p hg
    simpa only [d1958, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10963 (p : Pattern) (guard : d1961 p = 1) : d701 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10914 p hg
    simpa only [d1961, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10964 (p : Pattern) (guard : d1962 p = 1) : d702 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d1962, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10963 p hg
    simpa only [d1962, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10965 (p : Pattern) (guard : d1963 p = 1) : d702 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10962 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10964 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10966 (p : Pattern) (guard : d0 p = 1) : d701 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10967 (p : Pattern) (guard : d1966 p = 1) : d702 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10917 p hg
    simpa only [d1966, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10966 p hg
    simpa only [d1966, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10968 (p : Pattern) (guard : d1967 p = 1) : d702 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10964 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10967 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10969 (p : Pattern) (guard : d1968 p = 1) : d702 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10965 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10968 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10970 (p : Pattern) (guard : d1951 p = 1) : d11 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7888 p hg
    simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10971 (p : Pattern) (guard : d1956 p = 1) : d698 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10970 p hg
    simpa only [d1956, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2377 p hg
    simpa only [d1956, d698, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10972 (p : Pattern) (guard : d1957 p = 1) : d699 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10910 p hg
    simpa only [d1957, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d1957, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10973 (p : Pattern) (guard : d1962 p = 1) : d702 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10972 p hg
    simpa only [d1962, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10963 p hg
    simpa only [d1962, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10974 (p : Pattern) (guard : d1967 p = 1) : d702 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10973 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10967 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10975 (p : Pattern) (guard : d1971 p = 1) : d702 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10967 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10976 (p : Pattern) (guard : d1972 p = 1) : d702 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10974 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10975 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10977 (p : Pattern) (guard : d1973 p = 1) : d702 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10969 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10976 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10978 (p : Pattern) (guard : d1974 p = 1) : d703 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10960 p hg
    simpa only [d1974, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10977 p hg
    simpa only [d1974, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10979 (p : Pattern) (guard : d1975 p = 1) : d704 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d704, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10940 p hg
    simpa only [d1975, d704, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d704, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10978 p hg
    simpa only [d1975, d704, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10980 (p : Pattern) (guard : d1957 p = 1) : d698 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10953 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10981 (p : Pattern) (guard : d1961 p = 1) : d705 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10897 p hg
    simpa only [d1961, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10982 (p : Pattern) (guard : d1962 p = 1) : d706 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10980 p hg
    simpa only [d1962, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10981 p hg
    simpa only [d1962, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10983 (p : Pattern) (guard : d1961 p = 1) : d698 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10897 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10916 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10984 (p : Pattern) (guard : d1966 p = 1) : d706 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10983 p hg
    simpa only [d1966, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1966, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10985 (p : Pattern) (guard : d1967 p = 1) : d706 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10982 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10984 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10986 (p : Pattern) (guard : d1968 p = 1) : d707 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d707, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10929 p hg
    simpa only [d1968, d707, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d707, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10985 p hg
    simpa only [d1968, d707, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10987 (p : Pattern) (guard : d1969 p = 1) : d708 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10920 p hg
    simpa only [d1969, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10986 p hg
    simpa only [d1969, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10988 (p : Pattern) (guard : d1951 p = 1) : d5 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7883 p hg
    simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10989 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10990 (p : Pattern) (guard : d1956 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d1956, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d1956, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10991 (p : Pattern) (guard : d1957 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10926 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10992 (p : Pattern) (guard : d1962 p = 1) : d700 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d1962, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10917 p hg
    simpa only [d1962, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10993 (p : Pattern) (guard : d1967 p = 1) : d700 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10936 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10994 (p : Pattern) (guard : d1961 p = 1) : d705 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d1961, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10995 (p : Pattern) (guard : d1966 p = 1) : d705 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10996 (p : Pattern) (guard : d1971 p = 1) : d705 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10995 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10997 (p : Pattern) (guard : d1972 p = 1) : d709 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d709, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d1972, d709, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d709, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d1972, d709, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10998 (p : Pattern) (guard : d1973 p = 1) : d710 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10938 p hg
    simpa only [d1973, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10997 p hg
    simpa only [d1973, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10999 (p : Pattern) (guard : d1974 p = 1) : d711 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10987 p hg
    simpa only [d1974, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10998 p hg
    simpa only [d1974, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11000 (p : Pattern) (guard : d1962 p = 1) : d699 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10972 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10917 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11001 (p : Pattern) (guard : d1967 p = 1) : d699 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11000 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10957 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11002 (p : Pattern) (guard : d1966 p = 1) : d705 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10981 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11003 (p : Pattern) (guard : d1971 p = 1) : d705 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11002 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11004 (p : Pattern) (guard : d1972 p = 1) : d712 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d712, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11001 p hg
    simpa only [d1972, d712, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d712, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d1972, d712, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11005 (p : Pattern) (guard : d1973 p = 1) : d713 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10959 p hg
    simpa only [d1973, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11004 p hg
    simpa only [d1973, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11006 (p : Pattern) (guard : d0 p = 1) : d698 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11007 (p : Pattern) (guard : d1961 p = 1) : d699 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10931 p hg
    simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11006 p hg
    simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11008 (p : Pattern) (guard : d1966 p = 1) : d702 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d1966, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10966 p hg
    simpa only [d1966, d702, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11009 (p : Pattern) (guard : d1971 p = 1) : d702 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11008 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11010 (p : Pattern) (guard : d1976 p = 1) : d714 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d714, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11009 p hg
    simpa only [d1976, d714, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d714, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1976, d714, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11011 (p : Pattern) (guard : d1977 p = 1) : d715 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10976 p hg
    simpa only [d1977, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11010 p hg
    simpa only [d1977, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11012 (p : Pattern) (guard : d1978 p = 1) : d716 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11005 p hg
    simpa only [d1978, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11011 p hg
    simpa only [d1978, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11013 (p : Pattern) (guard : d1979 p = 1) : d717 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d717, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10999 p hg
    simpa only [d1979, d717, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d717, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11012 p hg
    simpa only [d1979, d717, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11014 (p : Pattern) (guard : d1980 p = 1) : d718 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10979 p hg
    simpa only [d1980, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11013 p hg
    simpa only [d1980, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11015 (p : Pattern) (guard : d1958 p = 1) : d719 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10927 p hg
    simpa only [d1958, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10961 p hg
    simpa only [d1958, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11016 (p : Pattern) (guard : d1962 p = 1) : d719 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10915 p hg
    simpa only [d1962, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10963 p hg
    simpa only [d1962, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11017 (p : Pattern) (guard : d1963 p = 1) : d719 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11015 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11016 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11018 (p : Pattern) (guard : d1962 p = 1) : d719 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d719, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10932 p hg
    simpa only [d1962, d719, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d719, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10963 p hg
    simpa only [d1962, d719, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11019 (p : Pattern) (guard : d1966 p = 1) : d719 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10935 p hg
    simpa only [d1966, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10966 p hg
    simpa only [d1966, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11020 (p : Pattern) (guard : d1967 p = 1) : d719 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11018 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11019 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11021 (p : Pattern) (guard : d1968 p = 1) : d719 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11017 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11020 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11022 (p : Pattern) (guard : d1962 p = 1) : d719 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d1962, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10963 p hg
    simpa only [d1962, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11023 (p : Pattern) (guard : d1967 p = 1) : d719 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11022 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11019 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11024 (p : Pattern) (guard : d0 p = 1) : d697 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11025 (p : Pattern) (guard : d1961 p = 1) : d697 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10931 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11024 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11026 (p : Pattern) (guard : d1966 p = 1) : d719 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d719, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11025 p hg
    simpa only [d1966, d719, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d719, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10966 p hg
    simpa only [d1966, d719, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11027 (p : Pattern) (guard : d1971 p = 1) : d719 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11026 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7739 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11028 (p : Pattern) (guard : d1972 p = 1) : d719 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11023 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11027 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11029 (p : Pattern) (guard : d1973 p = 1) : d719 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11021 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11028 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11030 (p : Pattern) (guard : d1974 p = 1) : d720 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10939 p hg
    simpa only [d1974, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11029 p hg
    simpa only [d1974, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11031 (p : Pattern) (guard : d1953 p = 1) : d698 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10943 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10953 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11032 (p : Pattern) (guard : d1957 p = 1) : d705 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10883 p hg
    simpa only [d1957, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11033 (p : Pattern) (guard : d1958 p = 1) : d706 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d1958, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d1958, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11034 (p : Pattern) (guard : d1957 p = 1) : d698 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10883 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10897 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11035 (p : Pattern) (guard : d1962 p = 1) : d706 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d1962, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10981 p hg
    simpa only [d1962, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11036 (p : Pattern) (guard : d1963 p = 1) : d706 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11037 (p : Pattern) (guard : d1967 p = 1) : d706 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10984 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11038 (p : Pattern) (guard : d1968 p = 1) : d706 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11039 (p : Pattern) (guard : d1971 p = 1) : d706 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10984 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7722 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11040 (p : Pattern) (guard : d1972 p = 1) : d706 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10985 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11041 (p : Pattern) (guard : d1973 p = 1) : d706 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11038 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11040 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11042 (p : Pattern) (guard : d1961 p = 1) : d698 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11006 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11043 (p : Pattern) (guard : d1966 p = 1) : d706 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11042 p hg
    simpa only [d1966, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1966, d706, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11044 (p : Pattern) (guard : d1971 p = 1) : d706 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11043 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7722 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11045 (p : Pattern) (guard : d1976 p = 1) : d706 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11044 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7722 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11046 (p : Pattern) (guard : d1977 p = 1) : d706 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11040 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11045 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11047 (p : Pattern) (guard : d1978 p = 1) : d706 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11041 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11048 (p : Pattern) (guard : d1979 p = 1) : d721 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d721, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11030 p hg
    simpa only [d1979, d721, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d721, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11047 p hg
    simpa only [d1979, d721, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11049 (p : Pattern) (guard : d0 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11050 (p : Pattern) (guard : d1961 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11049 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11051 (p : Pattern) (guard : d1966 p = 1) : d719 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d1966, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10966 p hg
    simpa only [d1966, d719, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11052 (p : Pattern) (guard : d1971 p = 1) : d719 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11051 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7739 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11053 (p : Pattern) (guard : d0 p = 1) : d705 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11054 (p : Pattern) (guard : d1976 p = 1) : d722 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d722, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11052 p hg
    simpa only [d1976, d722, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d722, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11053 p hg
    simpa only [d1976, d722, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11055 (p : Pattern) (guard : d1977 p = 1) : d723 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11028 p hg
    simpa only [d1977, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11054 p hg
    simpa only [d1977, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11056 (p : Pattern) (guard : d1978 p = 1) : d724 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10998 p hg
    simpa only [d1978, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11055 p hg
    simpa only [d1978, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11057 (p : Pattern) (guard : d1976 p = 1) : d725 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d725, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11044 p hg
    simpa only [d1976, d725, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d725, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d725, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11058 (p : Pattern) (guard : d1977 p = 1) : d726 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11040 p hg
    simpa only [d1977, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11057 p hg
    simpa only [d1977, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11059 (p : Pattern) (guard : d1976 p = 1) : d705 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
