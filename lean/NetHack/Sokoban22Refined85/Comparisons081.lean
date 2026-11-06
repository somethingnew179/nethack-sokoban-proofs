/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons080
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11340 (p : Pattern) (guard : d4206 p = 1) : d161 p ≤ (0 : Int) + d4923 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d161, d4923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11339 p hg
    simpa only [d161, d4923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d161, d4923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d161, d4923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11341 (p : Pattern) (guard : d4206 p = 1) : d162 p ≤ (0 : Int) + d4924 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d162, d4924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11340 p hg
    simpa only [d162, d4924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d162, d4924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d162, d4924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11342 (p : Pattern) (guard : d4206 p = 1) : d163 p ≤ (0 : Int) + d4925 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d163, d4925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11336 p hg
    simpa only [d163, d4925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d163, d4925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11341 p hg
    simpa only [d163, d4925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11343 (p : Pattern) (guard : d4206 p = 1) : d164 p ≤ (0 : Int) + d4926 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d164, d4926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11337 p hg
    simpa only [d164, d4926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d164, d4926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11342 p hg
    simpa only [d164, d4926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11344 (p : Pattern) (guard : d4206 p = 1) : d165 p ≤ (0 : Int) + d4927 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d165, d4927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11336 p hg
    simpa only [d165, d4927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d165, d4927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d165, d4927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11345 (p : Pattern) (guard : d4206 p = 1) : d166 p ≤ (0 : Int) + d4928 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d166, d4928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11337 p hg
    simpa only [d166, d4928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d166, d4928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11344 p hg
    simpa only [d166, d4928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11346 (p : Pattern) (guard : d4206 p = 1) : d167 p ≤ (0 : Int) + d4929 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d167, d4929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11343 p hg
    simpa only [d167, d4929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d167, d4929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11345 p hg
    simpa only [d167, d4929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11347 (p : Pattern) (guard : d4206 p = 1) : d168 p ≤ (0 : Int) + d4930 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d168, d4930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11285 p hg
    simpa only [d168, d4930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d168, d4930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11346 p hg
    simpa only [d168, d4930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11348 (p : Pattern) (guard : d4206 p = 1) : d169 p ≤ (0 : Int) + d4931 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d169, d4931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11285 p hg
    simpa only [d169, d4931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d169, d4931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11347 p hg
    simpa only [d169, d4931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11349 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1210 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11350 (p : Pattern) (guard : d4206 p = 1) : d170 p ≤ (0 : Int) + d36 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11349 p hg
    simpa only [d4206, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11222 p hg
    simpa only [d4206, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11351 (p : Pattern) (guard : d4206 p = 1) : d171 p ≤ (0 : Int) + d4255 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d171, d4255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11238 p hg
    simpa only [d171, d4255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d171, d4255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11350 p hg
    simpa only [d171, d4255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11352 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1534 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11353 (p : Pattern) (guard : d4206 p = 1) : d172 p ≤ (0 : Int) + d41 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11352 p hg
    simpa only [d4206, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11226 p hg
    simpa only [d4206, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11354 (p : Pattern) (guard : d4206 p = 1) : d173 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d4206, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11355 (p : Pattern) (guard : d4206 p = 1) : d174 p ≤ (0 : Int) + d4218 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d174, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11353 p hg
    simpa only [d174, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d174, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11354 p hg
    simpa only [d174, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11356 (p : Pattern) (guard : d4206 p = 1) : d175 p ≤ (0 : Int) + d4257 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d175, d4257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11351 p hg
    simpa only [d175, d4257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d175, d4257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11355 p hg
    simpa only [d175, d4257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11357 (p : Pattern) (guard : d4206 p = 1) : d176 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11249 p hg
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11354 p hg
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11358 (p : Pattern) (guard : d4206 p = 1) : d177 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11357 p hg
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11256 p hg
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11359 (p : Pattern) (guard : d4206 p = 1) : d178 p ≤ (0 : Int) + d4903 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d178, d4903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11356 p hg
    simpa only [d178, d4903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d178, d4903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11358 p hg
    simpa only [d178, d4903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11360 (p : Pattern) (guard : d4206 p = 1) : d179 p ≤ (0 : Int) + d4904 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d179, d4904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11217 p hg
    simpa only [d179, d4904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d179, d4904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11359 p hg
    simpa only [d179, d4904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11361 (p : Pattern) (guard : d4206 p = 1) : d180 p ≤ (0 : Int) + d4261 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d180, d4261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11350 p hg
    simpa only [d180, d4261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d180, d4261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11228 p hg
    simpa only [d180, d4261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11362 (p : Pattern) (guard : d4206 p = 1) : d181 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11354 p hg
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11255 p hg
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11363 (p : Pattern) (guard : d4206 p = 1) : d182 p ≤ (0 : Int) + d4262 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d182, d4262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11361 p hg
    simpa only [d182, d4262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d182, d4262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11362 p hg
    simpa only [d182, d4262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11364 (p : Pattern) (guard : d4206 p = 1) : d183 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11354 p hg
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11365 (p : Pattern) (guard : d4206 p = 1) : d184 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11364 p hg
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11366 (p : Pattern) (guard : d4206 p = 1) : d185 p ≤ (0 : Int) + d4905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d185, d4905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11363 p hg
    simpa only [d185, d4905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d185, d4905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11365 p hg
    simpa only [d185, d4905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11367 (p : Pattern) (guard : d4206 p = 1) : d186 p ≤ (0 : Int) + d4906 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d186, d4906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11248 p hg
    simpa only [d186, d4906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d186, d4906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11366 p hg
    simpa only [d186, d4906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11368 (p : Pattern) (guard : d4206 p = 1) : d187 p ≤ (0 : Int) + d4907 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d187, d4907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11360 p hg
    simpa only [d187, d4907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d187, d4907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11367 p hg
    simpa only [d187, d4907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11369 (p : Pattern) (guard : d4206 p = 1) : d188 p ≤ (0 : Int) + d4256 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d188, d4256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11208 p hg
    simpa only [d188, d4256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d188, d4256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11263 p hg
    simpa only [d188, d4256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11370 (p : Pattern) (guard : d4206 p = 1) : d189 p ≤ (0 : Int) + d4258 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d189, d4258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11369 p hg
    simpa only [d189, d4258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d189, d4258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11264 p hg
    simpa only [d189, d4258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11371 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11372 (p : Pattern) (guard : d0 p = 1) : d192 p ≤ (0 : Int) + d192 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11373 (p : Pattern) (guard : d4206 p = 1) : d193 p ≤ (0 : Int) + d192 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11371 p hg
    simpa only [d4206, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11372 p hg
    simpa only [d4206, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11374 (p : Pattern) (guard : d4206 p = 1) : d194 p ≤ (0 : Int) + d4932 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d194, d4932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11210 p hg
    simpa only [d194, d4932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d194, d4932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11373 p hg
    simpa only [d194, d4932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11375 (p : Pattern) (guard : d4206 p = 1) : d195 p ≤ (0 : Int) + d4933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d195, d4933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11374 p hg
    simpa only [d195, d4933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d195, d4933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d195, d4933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11376 (p : Pattern) (guard : d4206 p = 1) : d196 p ≤ (0 : Int) + d4934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d196, d4934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11375 p hg
    simpa only [d196, d4934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d196, d4934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d196, d4934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11377 (p : Pattern) (guard : d4206 p = 1) : d197 p ≤ (0 : Int) + d4935 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d197, d4935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11370 p hg
    simpa only [d197, d4935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d197, d4935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11376 p hg
    simpa only [d197, d4935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11378 (p : Pattern) (guard : d4206 p = 1) : d198 p ≤ (0 : Int) + d4259 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d198, d4259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11210 p hg
    simpa only [d198, d4259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d198, d4259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11245 p hg
    simpa only [d198, d4259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11379 (p : Pattern) (guard : d4206 p = 1) : d199 p ≤ (0 : Int) + d4260 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d199, d4260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11238 p hg
    simpa only [d199, d4260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d199, d4260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11378 p hg
    simpa only [d199, d4260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11380 (p : Pattern) (guard : d4206 p = 1) : d200 p ≤ (0 : Int) + d4263 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d200, d4263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11379 p hg
    simpa only [d200, d4263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d200, d4263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11268 p hg
    simpa only [d200, d4263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11381 (p : Pattern) (guard : d4206 p = 1) : d201 p ≤ (0 : Int) + d4936 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d201, d4936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11373 p hg
    simpa only [d201, d4936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d201, d4936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d201, d4936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11382 (p : Pattern) (guard : d4206 p = 1) : d202 p ≤ (0 : Int) + d4937 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d202, d4937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11381 p hg
    simpa only [d202, d4937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d202, d4937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d202, d4937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11383 (p : Pattern) (guard : d4206 p = 1) : d203 p ≤ (0 : Int) + d4938 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d203, d4938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11382 p hg
    simpa only [d203, d4938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d203, d4938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d203, d4938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11384 (p : Pattern) (guard : d4206 p = 1) : d204 p ≤ (0 : Int) + d4939 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d204, d4939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11380 p hg
    simpa only [d204, d4939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d204, d4939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11383 p hg
    simpa only [d204, d4939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11385 (p : Pattern) (guard : d4206 p = 1) : d205 p ≤ (0 : Int) + d4940 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d205, d4940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11377 p hg
    simpa only [d205, d4940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d205, d4940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11384 p hg
    simpa only [d205, d4940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11386 (p : Pattern) (guard : d4206 p = 1) : d206 p ≤ (0 : Int) + d4941 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d206, d4941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11368 p hg
    simpa only [d206, d4941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d206, d4941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11385 p hg
    simpa only [d206, d4941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11387 (p : Pattern) (guard : d4206 p = 1) : d207 p ≤ (0 : Int) + d4942 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d207, d4942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11385 p hg
    simpa only [d207, d4942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d207, d4942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d207, d4942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11388 (p : Pattern) (guard : d4206 p = 1) : d208 p ≤ (0 : Int) + d4943 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d208, d4943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11386 p hg
    simpa only [d208, d4943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d208, d4943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11387 p hg
    simpa only [d208, d4943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11389 (p : Pattern) (guard : d4206 p = 1) : d209 p ≤ (0 : Int) + d4944 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d209, d4944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11282 p hg
    simpa only [d209, d4944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d209, d4944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11388 p hg
    simpa only [d209, d4944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11390 (p : Pattern) (guard : d4206 p = 1) : d210 p ≤ (0 : Int) + d4945 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d210, d4945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11285 p hg
    simpa only [d210, d4945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d210, d4945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11389 p hg
    simpa only [d210, d4945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11391 (p : Pattern) (guard : d4206 p = 1) : d211 p ≤ (0 : Int) + d4270 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d211, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11289 p hg
    simpa only [d211, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d211, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d211, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11392 (p : Pattern) (guard : d4206 p = 1) : d212 p ≤ (0 : Int) + d4271 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d212, d4271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11311 p hg
    simpa only [d212, d4271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d212, d4271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11391 p hg
    simpa only [d212, d4271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11393 (p : Pattern) (guard : d4206 p = 1) : d213 p ≤ (0 : Int) + d4272 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d213, d4272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11391 p hg
    simpa only [d213, d4272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d213, d4272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d213, d4272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11394 (p : Pattern) (guard : d4206 p = 1) : d214 p ≤ (0 : Int) + d4273 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d214, d4273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11392 p hg
    simpa only [d214, d4273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d214, d4273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11393 p hg
    simpa only [d214, d4273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11395 (p : Pattern) (guard : d4206 p = 1) : d215 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11303 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11396 (p : Pattern) (guard : d4206 p = 1) : d216 p ≤ (0 : Int) + d4282 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d216, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11318 p hg
    simpa only [d216, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d216, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11395 p hg
    simpa only [d216, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11397 (p : Pattern) (guard : d4206 p = 1) : d217 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11395 p hg
    simpa only [d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11398 (p : Pattern) (guard : d4206 p = 1) : d218 p ≤ (0 : Int) + d4920 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d218, d4920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11396 p hg
    simpa only [d218, d4920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d218, d4920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11397 p hg
    simpa only [d218, d4920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11399 (p : Pattern) (guard : d4206 p = 1) : d219 p ≤ (0 : Int) + d4946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d219, d4946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11394 p hg
    simpa only [d219, d4946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d219, d4946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11398 p hg
    simpa only [d219, d4946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11400 (p : Pattern) (guard : d4206 p = 1) : d220 p ≤ (0 : Int) + d4947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d220, d4947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11309 p hg
    simpa only [d220, d4947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d220, d4947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11399 p hg
    simpa only [d220, d4947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11401 (p : Pattern) (guard : d4206 p = 1) : d221 p ≤ (0 : Int) + d4946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d221, d4946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11394 p hg
    simpa only [d221, d4946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d221, d4946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11334 p hg
    simpa only [d221, d4946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11402 (p : Pattern) (guard : d4206 p = 1) : d222 p ≤ (0 : Int) + d4947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d222, d4947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11331 p hg
    simpa only [d222, d4947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d222, d4947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11401 p hg
    simpa only [d222, d4947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11403 (p : Pattern) (guard : d4206 p = 1) : d223 p ≤ (0 : Int) + d4947 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11400 p hg
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11402 p hg
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11404 (p : Pattern) (guard : d4206 p = 1) : d224 p ≤ (0 : Int) + d4948 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d224, d4948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11402 p hg
    simpa only [d224, d4948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d224, d4948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11341 p hg
    simpa only [d224, d4948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11405 (p : Pattern) (guard : d4206 p = 1) : d225 p ≤ (0 : Int) + d4949 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d225, d4949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11403 p hg
    simpa only [d225, d4949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d225, d4949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11404 p hg
    simpa only [d225, d4949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11406 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11407 (p : Pattern) (guard : d4206 p = 1) : d226 p ≤ (0 : Int) + d121 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11406 p hg
    simpa only [d4206, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11299 p hg
    simpa only [d4206, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11408 (p : Pattern) (guard : d4206 p = 1) : d227 p ≤ (0 : Int) + d4916 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d227, d4916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11310 p hg
    simpa only [d227, d4916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d227, d4916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11407 p hg
    simpa only [d227, d4916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11409 (p : Pattern) (guard : d4206 p = 1) : d228 p ≤ (0 : Int) + d4917 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d228, d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11408 p hg
    simpa only [d228, d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d228, d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11395 p hg
    simpa only [d228, d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11410 (p : Pattern) (guard : d4206 p = 1) : d229 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d4206, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11411 (p : Pattern) (guard : d4206 p = 1) : d230 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11410 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11412 (p : Pattern) (guard : d4206 p = 1) : d231 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11411 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11413 (p : Pattern) (guard : d4206 p = 1) : d232 p ≤ (0 : Int) + d4918 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d232, d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11409 p hg
    simpa only [d232, d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d232, d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11412 p hg
    simpa only [d232, d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11414 (p : Pattern) (guard : d4206 p = 1) : d233 p ≤ (0 : Int) + d4919 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d233, d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11294 p hg
    simpa only [d233, d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d233, d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11413 p hg
    simpa only [d233, d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11415 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1417 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11416 (p : Pattern) (guard : d4206 p = 1) : d234 p ≤ (0 : Int) + d121 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11415 p hg
    simpa only [d4206, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11299 p hg
    simpa only [d4206, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11417 (p : Pattern) (guard : d4206 p = 1) : d235 p ≤ (0 : Int) + d4281 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d235, d4281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11416 p hg
    simpa only [d235, d4281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d235, d4281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11303 p hg
    simpa only [d235, d4281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11418 (p : Pattern) (guard : d4206 p = 1) : d236 p ≤ (0 : Int) + d4282 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d236, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11417 p hg
    simpa only [d236, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d236, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11411 p hg
    simpa only [d236, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11419 (p : Pattern) (guard : d4206 p = 1) : d237 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11234 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11420 (p : Pattern) (guard : d4206 p = 1) : d238 p ≤ (0 : Int) + d4920 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d238, d4920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11418 p hg
    simpa only [d238, d4920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d238, d4920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11419 p hg
    simpa only [d238, d4920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11421 (p : Pattern) (guard : d4206 p = 1) : d239 p ≤ (0 : Int) + d4946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d239, d4946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11394 p hg
    simpa only [d239, d4946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d239, d4946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11420 p hg
    simpa only [d239, d4946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11422 (p : Pattern) (guard : d4206 p = 1) : d240 p ≤ (0 : Int) + d4947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d240, d4947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11414 p hg
    simpa only [d240, d4947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d240, d4947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11421 p hg
    simpa only [d240, d4947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11423 (p : Pattern) (guard : d4206 p = 1) : d241 p ≤ (0 : Int) + d4277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d241, d4277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11310 p hg
    simpa only [d241, d4277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d241, d4277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11245 p hg
    simpa only [d241, d4277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11424 (p : Pattern) (guard : d4206 p = 1) : d242 p ≤ (0 : Int) + d4278 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d242, d4278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11287 p hg
    simpa only [d242, d4278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d242, d4278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11423 p hg
    simpa only [d242, d4278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11425 (p : Pattern) (guard : d4206 p = 1) : d243 p ≤ (0 : Int) + d4279 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d243, d4279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11424 p hg
    simpa only [d243, d4279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d243, d4279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11315 p hg
    simpa only [d243, d4279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11426 (p : Pattern) (guard : d4206 p = 1) : d244 p ≤ (0 : Int) + d4950 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d244, d4950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11425 p hg
    simpa only [d244, d4950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d244, d4950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11334 p hg
    simpa only [d244, d4950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11427 (p : Pattern) (guard : d4206 p = 1) : d245 p ≤ (0 : Int) + d4280 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d245, d4280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11310 p hg
    simpa only [d245, d4280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d245, d4280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11391 p hg
    simpa only [d245, d4280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11428 (p : Pattern) (guard : d4206 p = 1) : d246 p ≤ (0 : Int) + d4283 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d246, d4283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11427 p hg
    simpa only [d246, d4283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d246, d4283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11333 p hg
    simpa only [d246, d4283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11429 (p : Pattern) (guard : d4206 p = 1) : d247 p ≤ (0 : Int) + d4951 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d247, d4951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11215 p hg
    simpa only [d247, d4951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d247, d4951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d247, d4951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11430 (p : Pattern) (guard : d4206 p = 1) : d248 p ≤ (0 : Int) + d4952 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d248, d4952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11429 p hg
    simpa only [d248, d4952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d248, d4952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d248, d4952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11431 (p : Pattern) (guard : d4206 p = 1) : d249 p ≤ (0 : Int) + d4953 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d249, d4953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11428 p hg
    simpa only [d249, d4953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d249, d4953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11430 p hg
    simpa only [d249, d4953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11432 (p : Pattern) (guard : d4206 p = 1) : d250 p ≤ (0 : Int) + d4954 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d250, d4954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11426 p hg
    simpa only [d250, d4954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d250, d4954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11431 p hg
    simpa only [d250, d4954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11433 (p : Pattern) (guard : d4206 p = 1) : d251 p ≤ (0 : Int) + d4955 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d251, d4955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11422 p hg
    simpa only [d251, d4955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d251, d4955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11432 p hg
    simpa only [d251, d4955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11434 (p : Pattern) (guard : d4206 p = 1) : d252 p ≤ (0 : Int) + d4286 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d252, d4286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11310 p hg
    simpa only [d252, d4286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d252, d4286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11214 p hg
    simpa only [d252, d4286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11435 (p : Pattern) (guard : d4206 p = 1) : d253 p ≤ (0 : Int) + d4287 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d253, d4287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11287 p hg
    simpa only [d253, d4287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d253, d4287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11434 p hg
    simpa only [d253, d4287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11436 (p : Pattern) (guard : d4206 p = 1) : d254 p ≤ (0 : Int) + d4288 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d254, d4288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11289 p hg
    simpa only [d254, d4288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d254, d4288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11214 p hg
    simpa only [d254, d4288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11437 (p : Pattern) (guard : d4206 p = 1) : d255 p ≤ (0 : Int) + d4289 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d255, d4289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d255, d4289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d255, d4289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d255, d4289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11438 (p : Pattern) (guard : d4206 p = 1) : d256 p ≤ (0 : Int) + d4290 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d256, d4290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11435 p hg
    simpa only [d256, d4290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d256, d4290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11437 p hg
    simpa only [d256, d4290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11439 (p : Pattern) (guard : d4206 p = 1) : d257 p ≤ (0 : Int) + d4956 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d257, d4956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11327 p hg
    simpa only [d257, d4956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d257, d4956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11245 p hg
    simpa only [d257, d4956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11440 (p : Pattern) (guard : d4206 p = 1) : d258 p ≤ (0 : Int) + d4957 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d258, d4957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11439 p hg
    simpa only [d258, d4957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d258, d4957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d258, d4957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11441 (p : Pattern) (guard : d4206 p = 1) : d259 p ≤ (0 : Int) + d4958 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d259, d4958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11440 p hg
    simpa only [d259, d4958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d259, d4958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d259, d4958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11442 (p : Pattern) (guard : d4206 p = 1) : d260 p ≤ (0 : Int) + d4959 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d260, d4959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11438 p hg
    simpa only [d260, d4959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d260, d4959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11441 p hg
    simpa only [d260, d4959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11443 (p : Pattern) (guard : d4206 p = 1) : d261 p ≤ (0 : Int) + d4960 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d261, d4960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11442 p hg
    simpa only [d261, d4960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d261, d4960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11431 p hg
    simpa only [d261, d4960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11444 (p : Pattern) (guard : d4206 p = 1) : d262 p ≤ (0 : Int) + d4961 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d262, d4961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11443 p hg
    simpa only [d262, d4961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d262, d4961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d262, d4961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11445 (p : Pattern) (guard : d4206 p = 1) : d263 p ≤ (0 : Int) + d4962 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d263, d4962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11433 p hg
    simpa only [d263, d4962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d263, d4962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11444 p hg
    simpa only [d263, d4962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11446 (p : Pattern) (guard : d4206 p = 1) : d264 p ≤ (0 : Int) + d4963 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d264, d4963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11405 p hg
    simpa only [d264, d4963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d264, d4963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11445 p hg
    simpa only [d264, d4963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11447 (p : Pattern) (guard : d4206 p = 1) : d265 p ≤ (0 : Int) + d4964 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d265, d4964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11285 p hg
    simpa only [d265, d4964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d265, d4964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11446 p hg
    simpa only [d265, d4964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11448 (p : Pattern) (guard : d4206 p = 1) : d266 p ≤ (0 : Int) + d4965 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d266, d4965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11390 p hg
    simpa only [d266, d4965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d266, d4965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11447 p hg
    simpa only [d266, d4965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11449 (p : Pattern) (guard : d4206 p = 1) : d267 p ≤ (0 : Int) + d4966 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d267, d4966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11348 p hg
    simpa only [d267, d4966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d267, d4966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11448 p hg
    simpa only [d267, d4966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11450 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11451 (p : Pattern) (guard : d4474 p = 1) : d14 p ≤ (0 : Int) + d1682 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11450 p hg
    simpa only [d4474, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11452 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d1687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11453 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1688 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11451 p hg
    simpa only [d4967, d16, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11452 p hg
    simpa only [d4967, d16, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11454 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d333 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11455 (p : Pattern) (guard : d4474 p = 1) : d14 p ≤ (0 : Int) + d1689 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11454 p hg
    simpa only [d4474, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11456 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1690 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11455 p hg
    simpa only [d4967, d16, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11452 p hg
    simpa only [d4967, d16, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11457 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1691 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11453 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11456 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11458 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11459 (p : Pattern) (guard : d4474 p = 1) : d14 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d4474, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11460 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1692 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d16, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11452 p hg
    simpa only [d4967, d16, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11461 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11462 (p : Pattern) (guard : d4474 p = 1) : d18 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4474, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d4474, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11463 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (0 : Int) + d1697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11464 (p : Pattern) (guard : d4967 p = 1) : d20 p ≤ (0 : Int) + d1698 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d20, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d4967, d20, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d20, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11463 p hg
    simpa only [d4967, d20, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11465 (p : Pattern) (guard : d4967 p = 1) : d21 p ≤ (0 : Int) + d1699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d21, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11460 p hg
    simpa only [d21, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d21, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11464 p hg
    simpa only [d21, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11466 (p : Pattern) (guard : d4967 p = 1) : d22 p ≤ (0 : Int) + d1700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d22, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11457 p hg
    simpa only [d22, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d22, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11465 p hg
    simpa only [d22, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11467 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11468 (p : Pattern) (guard : d4474 p = 1) : d24 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d4474, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d4474, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11469 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (0 : Int) + d1705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11470 (p : Pattern) (guard : d4967 p = 1) : d26 p ≤ (0 : Int) + d1706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d26, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11468 p hg
    simpa only [d4967, d26, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d26, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11469 p hg
    simpa only [d4967, d26, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11471 (p : Pattern) (guard : d4967 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare11472 (p : Pattern) (guard : d4967 p = 1) : d27 p ≤ (0 : Int) + d1707 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d27, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11470 p hg
    simpa only [d27, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d27, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d27, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11473 (p : Pattern) (guard : d4967 p = 1) : d28 p ≤ (0 : Int) + d1708 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d28, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11465 p hg
    simpa only [d28, d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d28, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11472 p hg
    simpa only [d28, d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11474 (p : Pattern) (guard : d4967 p = 1) : d29 p ≤ (0 : Int) + d1709 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d29, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11466 p hg
    simpa only [d29, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d29, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11473 p hg
    simpa only [d29, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11475 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d1718 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11476 (p : Pattern) (guard : d4967 p = 1) : d33 p ≤ (0 : Int) + d1719 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d33, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d33, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d33, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11475 p hg
    simpa only [d4967, d33, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11477 (p : Pattern) (guard : d0 p = 1) : d36 p ≤ (0 : Int) + d1725 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11478 (p : Pattern) (guard : d4967 p = 1) : d37 p ≤ (0 : Int) + d1726 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d37, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d37, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d37, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11477 p hg
    simpa only [d4967, d37, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11479 (p : Pattern) (guard : d4967 p = 1) : d38 p ≤ (0 : Int) + d1727 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d38, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11476 p hg
    simpa only [d38, d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d38, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11478 p hg
    simpa only [d38, d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
