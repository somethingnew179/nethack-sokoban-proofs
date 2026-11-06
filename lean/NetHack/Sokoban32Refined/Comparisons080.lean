/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11200 (p : Pattern) (guard : d1963 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11197 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11199 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11201 (p : Pattern) (guard : d1964 p = 1) : d653 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11198 p hg
    simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11200 p hg
    simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11202 (p : Pattern) (guard : d1947 p = 1) : d13 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9586 p hg
    simpa only [d1947, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11203 (p : Pattern) (guard : d1952 p = 1) : d13 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11202 p hg
    simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9517 p hg
    simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11204 (p : Pattern) (guard : d1953 p = 1) : d653 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11154 p hg
    simpa only [d1953, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11203 p hg
    simpa only [d1953, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11205 (p : Pattern) (guard : d1958 p = 1) : d653 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11204 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11206 (p : Pattern) (guard : d1963 p = 1) : d653 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11205 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11199 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11207 (p : Pattern) (guard : d1966 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11174 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11208 (p : Pattern) (guard : d1967 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11199 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11207 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11209 (p : Pattern) (guard : d1968 p = 1) : d653 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11206 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11208 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11210 (p : Pattern) (guard : d1969 p = 1) : d653 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11201 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11209 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11211 (p : Pattern) (guard : d1957 p = 1) : d655 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11157 p hg
    simpa only [d1957, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11212 (p : Pattern) (guard : d1958 p = 1) : d656 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11204 p hg
    simpa only [d1958, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11211 p hg
    simpa only [d1958, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11213 (p : Pattern) (guard : d1961 p = 1) : d655 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11172 p hg
    simpa only [d1961, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11214 (p : Pattern) (guard : d1962 p = 1) : d656 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d1962, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11213 p hg
    simpa only [d1962, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11215 (p : Pattern) (guard : d1963 p = 1) : d656 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11212 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11214 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11216 (p : Pattern) (guard : d0 p = 1) : d655 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11217 (p : Pattern) (guard : d1966 p = 1) : d656 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11174 p hg
    simpa only [d1966, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11216 p hg
    simpa only [d1966, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11218 (p : Pattern) (guard : d1967 p = 1) : d656 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11214 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11217 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11219 (p : Pattern) (guard : d1968 p = 1) : d656 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11215 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11218 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11220 (p : Pattern) (guard : d1951 p = 1) : d13 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9605 p hg
    simpa only [d1951, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11221 (p : Pattern) (guard : d1956 p = 1) : d13 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11220 p hg
    simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11222 (p : Pattern) (guard : d1957 p = 1) : d653 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11169 p hg
    simpa only [d1957, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11221 p hg
    simpa only [d1957, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11223 (p : Pattern) (guard : d1962 p = 1) : d656 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11222 p hg
    simpa only [d1962, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11213 p hg
    simpa only [d1962, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11224 (p : Pattern) (guard : d1967 p = 1) : d656 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11223 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11217 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11225 (p : Pattern) (guard : d1971 p = 1) : d656 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11217 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11226 (p : Pattern) (guard : d1972 p = 1) : d656 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11224 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11225 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11227 (p : Pattern) (guard : d1973 p = 1) : d656 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11219 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11226 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11228 (p : Pattern) (guard : d1974 p = 1) : d657 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11210 p hg
    simpa only [d1974, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11227 p hg
    simpa only [d1974, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11229 (p : Pattern) (guard : d1975 p = 1) : d658 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d658, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11192 p hg
    simpa only [d1975, d658, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d658, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11228 p hg
    simpa only [d1975, d658, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11230 (p : Pattern) (guard : d1957 p = 1) : d13 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11203 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11221 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11231 (p : Pattern) (guard : d1961 p = 1) : d659 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11159 p hg
    simpa only [d1961, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11232 (p : Pattern) (guard : d1962 p = 1) : d660 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11230 p hg
    simpa only [d1962, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11231 p hg
    simpa only [d1962, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11233 (p : Pattern) (guard : d1961 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11159 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11234 (p : Pattern) (guard : d1966 p = 1) : d660 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11233 p hg
    simpa only [d1966, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1966, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11235 (p : Pattern) (guard : d1967 p = 1) : d660 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11232 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11234 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11236 (p : Pattern) (guard : d1968 p = 1) : d661 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d661, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11183 p hg
    simpa only [d1968, d661, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d661, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11235 p hg
    simpa only [d1968, d661, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11237 (p : Pattern) (guard : d1969 p = 1) : d662 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11177 p hg
    simpa only [d1969, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11236 p hg
    simpa only [d1969, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11238 (p : Pattern) (guard : d1951 p = 1) : d7 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9632 p hg
    simpa only [d1951, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11239 (p : Pattern) (guard : d1956 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11238 p hg
    simpa only [d1956, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1956, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11240 (p : Pattern) (guard : d1957 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11180 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11239 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11241 (p : Pattern) (guard : d1962 p = 1) : d654 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11240 p hg
    simpa only [d1962, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11174 p hg
    simpa only [d1962, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11242 (p : Pattern) (guard : d1967 p = 1) : d654 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11241 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11188 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11243 (p : Pattern) (guard : d1961 p = 1) : d659 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11221 p hg
    simpa only [d1961, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11244 (p : Pattern) (guard : d1966 p = 1) : d659 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11243 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11245 (p : Pattern) (guard : d1971 p = 1) : d659 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11244 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11246 (p : Pattern) (guard : d1972 p = 1) : d663 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d663, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11242 p hg
    simpa only [d1972, d663, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d663, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11245 p hg
    simpa only [d1972, d663, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11247 (p : Pattern) (guard : d1973 p = 1) : d664 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11190 p hg
    simpa only [d1973, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11246 p hg
    simpa only [d1973, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11248 (p : Pattern) (guard : d1974 p = 1) : d665 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11237 p hg
    simpa only [d1974, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11247 p hg
    simpa only [d1974, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11249 (p : Pattern) (guard : d1962 p = 1) : d653 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11222 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11174 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11250 (p : Pattern) (guard : d1967 p = 1) : d653 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11249 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11207 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11251 (p : Pattern) (guard : d1966 p = 1) : d659 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11231 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11252 (p : Pattern) (guard : d1971 p = 1) : d659 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11251 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11253 (p : Pattern) (guard : d1972 p = 1) : d666 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d666, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11250 p hg
    simpa only [d1972, d666, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d666, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11252 p hg
    simpa only [d1972, d666, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11254 (p : Pattern) (guard : d1973 p = 1) : d667 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11209 p hg
    simpa only [d1973, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11253 p hg
    simpa only [d1973, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11255 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11256 (p : Pattern) (guard : d1961 p = 1) : d653 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11184 p hg
    simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11255 p hg
    simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11257 (p : Pattern) (guard : d1966 p = 1) : d656 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11256 p hg
    simpa only [d1966, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11216 p hg
    simpa only [d1966, d656, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11258 (p : Pattern) (guard : d1971 p = 1) : d656 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11257 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11259 (p : Pattern) (guard : d1976 p = 1) : d668 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d668, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11258 p hg
    simpa only [d1976, d668, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d668, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1976, d668, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11260 (p : Pattern) (guard : d1977 p = 1) : d669 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11226 p hg
    simpa only [d1977, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11259 p hg
    simpa only [d1977, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11261 (p : Pattern) (guard : d1978 p = 1) : d670 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11254 p hg
    simpa only [d1978, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11260 p hg
    simpa only [d1978, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11262 (p : Pattern) (guard : d1979 p = 1) : d671 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d671, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11248 p hg
    simpa only [d1979, d671, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d671, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11261 p hg
    simpa only [d1979, d671, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11263 (p : Pattern) (guard : d1980 p = 1) : d672 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11229 p hg
    simpa only [d1980, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11262 p hg
    simpa only [d1980, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11264 (p : Pattern) (guard : d1958 p = 1) : d673 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11181 p hg
    simpa only [d1958, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11211 p hg
    simpa only [d1958, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11265 (p : Pattern) (guard : d1962 p = 1) : d673 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11173 p hg
    simpa only [d1962, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11213 p hg
    simpa only [d1962, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11266 (p : Pattern) (guard : d1963 p = 1) : d673 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11264 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11265 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11267 (p : Pattern) (guard : d1962 p = 1) : d673 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d673, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11185 p hg
    simpa only [d1962, d673, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d673, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11213 p hg
    simpa only [d1962, d673, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11268 (p : Pattern) (guard : d1966 p = 1) : d673 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11187 p hg
    simpa only [d1966, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11216 p hg
    simpa only [d1966, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11269 (p : Pattern) (guard : d1967 p = 1) : d673 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11267 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11268 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11270 (p : Pattern) (guard : d1968 p = 1) : d673 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11266 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11269 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11271 (p : Pattern) (guard : d1962 p = 1) : d673 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11240 p hg
    simpa only [d1962, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11213 p hg
    simpa only [d1962, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11272 (p : Pattern) (guard : d1967 p = 1) : d673 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11271 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11268 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11273 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11274 (p : Pattern) (guard : d1961 p = 1) : d7 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11184 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11273 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11275 (p : Pattern) (guard : d1966 p = 1) : d673 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d673, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11274 p hg
    simpa only [d1966, d673, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d673, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11216 p hg
    simpa only [d1966, d673, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11276 (p : Pattern) (guard : d1971 p = 1) : d673 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11275 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7151 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11277 (p : Pattern) (guard : d1972 p = 1) : d673 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11272 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11276 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11278 (p : Pattern) (guard : d1973 p = 1) : d673 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11270 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11277 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11279 (p : Pattern) (guard : d1974 p = 1) : d674 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11191 p hg
    simpa only [d1974, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11278 p hg
    simpa only [d1974, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11280 (p : Pattern) (guard : d1953 p = 1) : d13 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11194 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11203 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11281 (p : Pattern) (guard : d1957 p = 1) : d659 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11149 p hg
    simpa only [d1957, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11282 (p : Pattern) (guard : d1958 p = 1) : d660 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11280 p hg
    simpa only [d1958, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11281 p hg
    simpa only [d1958, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11283 (p : Pattern) (guard : d1957 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11149 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11159 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11284 (p : Pattern) (guard : d1962 p = 1) : d660 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11283 p hg
    simpa only [d1962, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11231 p hg
    simpa only [d1962, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11285 (p : Pattern) (guard : d1963 p = 1) : d660 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11282 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11284 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11286 (p : Pattern) (guard : d1967 p = 1) : d660 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11284 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11234 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11287 (p : Pattern) (guard : d1968 p = 1) : d660 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11285 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11286 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11288 (p : Pattern) (guard : d1971 p = 1) : d660 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11234 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11289 (p : Pattern) (guard : d1972 p = 1) : d660 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11235 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11288 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11290 (p : Pattern) (guard : d1973 p = 1) : d660 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11287 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11289 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11291 (p : Pattern) (guard : d1961 p = 1) : d13 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11221 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11255 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11292 (p : Pattern) (guard : d1966 p = 1) : d660 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11291 p hg
    simpa only [d1966, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1966, d660, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11293 (p : Pattern) (guard : d1971 p = 1) : d660 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11292 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11294 (p : Pattern) (guard : d1976 p = 1) : d660 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11293 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11295 (p : Pattern) (guard : d1977 p = 1) : d660 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11289 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11294 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11296 (p : Pattern) (guard : d1978 p = 1) : d660 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11290 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11295 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11297 (p : Pattern) (guard : d1979 p = 1) : d675 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d675, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11279 p hg
    simpa only [d1979, d675, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d675, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11296 p hg
    simpa only [d1979, d675, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11298 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11299 (p : Pattern) (guard : d1961 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11239 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11298 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11300 (p : Pattern) (guard : d1966 p = 1) : d673 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11299 p hg
    simpa only [d1966, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11216 p hg
    simpa only [d1966, d673, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11301 (p : Pattern) (guard : d1971 p = 1) : d673 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11300 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7151 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11302 (p : Pattern) (guard : d0 p = 1) : d659 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11303 (p : Pattern) (guard : d1976 p = 1) : d676 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d676, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11301 p hg
    simpa only [d1976, d676, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d676, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11302 p hg
    simpa only [d1976, d676, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11304 (p : Pattern) (guard : d1977 p = 1) : d677 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11277 p hg
    simpa only [d1977, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11303 p hg
    simpa only [d1977, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11305 (p : Pattern) (guard : d1978 p = 1) : d678 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11247 p hg
    simpa only [d1978, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11304 p hg
    simpa only [d1978, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11306 (p : Pattern) (guard : d1976 p = 1) : d679 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d679, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11293 p hg
    simpa only [d1976, d679, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d679, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d679, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11307 (p : Pattern) (guard : d1977 p = 1) : d680 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11289 p hg
    simpa only [d1977, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11306 p hg
    simpa only [d1977, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11308 (p : Pattern) (guard : d1976 p = 1) : d659 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11245 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11309 (p : Pattern) (guard : d0 p = 1) : d681 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11310 (p : Pattern) (guard : d1981 p = 1) : d682 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11308 p hg
    simpa only [d1981, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11309 p hg
    simpa only [d1981, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11311 (p : Pattern) (guard : d1982 p = 1) : d683 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11307 p hg
    simpa only [d1982, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11310 p hg
    simpa only [d1982, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11312 (p : Pattern) (guard : d1983 p = 1) : d684 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d684, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11305 p hg
    simpa only [d1983, d684, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d684, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11311 p hg
    simpa only [d1983, d684, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11313 (p : Pattern) (guard : d1984 p = 1) : d685 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11297 p hg
    simpa only [d1984, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11312 p hg
    simpa only [d1984, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11314 (p : Pattern) (guard : d1985 p = 1) : d686 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11263 p hg
    simpa only [d1985, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11313 p hg
    simpa only [d1985, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11315 (p : Pattern) (guard : d1966 p = 1) : d654 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11274 p hg
    simpa only [d1966, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1966, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11316 (p : Pattern) (guard : d1971 p = 1) : d654 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11315 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7492 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11317 (p : Pattern) (guard : d1972 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11242 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11316 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11318 (p : Pattern) (guard : d1973 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11190 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11317 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11319 (p : Pattern) (guard : d1974 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11191 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11318 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11320 (p : Pattern) (guard : d1971 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11207 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11321 (p : Pattern) (guard : d1972 p = 1) : d653 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11250 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11320 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11322 (p : Pattern) (guard : d1973 p = 1) : d653 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11209 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11321 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11323 (p : Pattern) (guard : d1976 p = 1) : d656 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11258 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11324 (p : Pattern) (guard : d1977 p = 1) : d656 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11226 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11323 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11325 (p : Pattern) (guard : d1978 p = 1) : d657 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11322 p hg
    simpa only [d1978, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11324 p hg
    simpa only [d1978, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11326 (p : Pattern) (guard : d1979 p = 1) : d658 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d658, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11319 p hg
    simpa only [d1979, d658, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d658, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11325 p hg
    simpa only [d1979, d658, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11327 (p : Pattern) (guard : d1966 p = 1) : d654 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11299 p hg
    simpa only [d1966, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1966, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11328 (p : Pattern) (guard : d1971 p = 1) : d654 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11327 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7492 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11329 (p : Pattern) (guard : d1976 p = 1) : d663 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d663, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11328 p hg
    simpa only [d1976, d663, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d663, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11302 p hg
    simpa only [d1976, d663, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11330 (p : Pattern) (guard : d1977 p = 1) : d664 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11317 p hg
    simpa only [d1977, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11329 p hg
    simpa only [d1977, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11331 (p : Pattern) (guard : d1978 p = 1) : d664 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11247 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11330 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11332 (p : Pattern) (guard : d1966 p = 1) : d653 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11256 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11333 (p : Pattern) (guard : d1971 p = 1) : d653 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11332 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11334 (p : Pattern) (guard : d1976 p = 1) : d666 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d666, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11333 p hg
    simpa only [d1976, d666, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d666, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1976, d666, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11335 (p : Pattern) (guard : d1977 p = 1) : d667 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11321 p hg
    simpa only [d1977, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11334 p hg
    simpa only [d1977, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11336 (p : Pattern) (guard : d0 p = 1) : d668 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11337 (p : Pattern) (guard : d1981 p = 1) : d669 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11323 p hg
    simpa only [d1981, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11336 p hg
    simpa only [d1981, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11338 (p : Pattern) (guard : d1982 p = 1) : d670 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11335 p hg
    simpa only [d1982, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11337 p hg
    simpa only [d1982, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11339 (p : Pattern) (guard : d1983 p = 1) : d687 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d687, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11331 p hg
    simpa only [d1983, d687, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d687, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11338 p hg
    simpa only [d1983, d687, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
