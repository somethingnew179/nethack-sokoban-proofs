/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4480 (p : Pattern) (guard : d854 p = 1) : d181 p ≤ (2 : Int) + d881 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d181, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d181, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d181, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d181, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4481 (p : Pattern) (guard : d854 p = 1) : d240 p ≤ (2 : Int) + d882 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d240, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d240, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d240, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d240, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4482 (p : Pattern) (guard : d854 p = 1) : d241 p ≤ (2 : Int) + d883 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d241, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4480 p hg
    simpa only [d241, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d241, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d241, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4483 (p : Pattern) (guard : d854 p = 1) : d242 p ≤ (2 : Int) + d884 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d242, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d242, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d242, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4482 p hg
    simpa only [d242, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4484 (p : Pattern) (guard : d854 p = 1) : d243 p ≤ (2 : Int) + d885 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d243, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4476 p hg
    simpa only [d243, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d243, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4483 p hg
    simpa only [d243, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4485 (p : Pattern) (guard : d854 p = 1) : d66 p ≤ (2 : Int) + d886 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4486 (p : Pattern) (guard : d854 p = 1) : d244 p ≤ (2 : Int) + d887 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d244, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4483 p hg
    simpa only [d244, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d244, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d244, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4487 (p : Pattern) (guard : d854 p = 1) : d245 p ≤ (2 : Int) + d888 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d245, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4484 p hg
    simpa only [d245, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d245, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4486 p hg
    simpa only [d245, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4488 (p : Pattern) (guard : d854 p = 1) : d137 p ≤ (2 : Int) + d889 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d137, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d137, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d137, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d137, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4489 (p : Pattern) (guard : d854 p = 1) : d139 p ≤ (2 : Int) + d890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d139, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d139, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d139, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4488 p hg
    simpa only [d139, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4490 (p : Pattern) (guard : d854 p = 1) : d153 p ≤ (2 : Int) + d891 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d153, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4449 p hg
    simpa only [d153, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d153, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d153, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4491 (p : Pattern) (guard : d854 p = 1) : d186 p ≤ (2 : Int) + d892 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d186, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4449 p hg
    simpa only [d186, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d186, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4490 p hg
    simpa only [d186, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4492 (p : Pattern) (guard : d854 p = 1) : d143 p ≤ (2 : Int) + d893 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d143, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d143, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d143, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4456 p hg
    simpa only [d143, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4493 (p : Pattern) (guard : d854 p = 1) : d144 p ≤ (2 : Int) + d894 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d144, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4488 p hg
    simpa only [d144, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d144, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4492 p hg
    simpa only [d144, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4494 (p : Pattern) (guard : d854 p = 1) : d146 p ≤ (2 : Int) + d895 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d146, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4471 p hg
    simpa only [d146, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d146, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d146, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4495 (p : Pattern) (guard : d854 p = 1) : d155 p ≤ (2 : Int) + d896 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d155, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4459 p hg
    simpa only [d155, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d155, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4494 p hg
    simpa only [d155, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4496 (p : Pattern) (guard : d854 p = 1) : d246 p ≤ (2 : Int) + d897 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d246, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4459 p hg
    simpa only [d246, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d246, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4495 p hg
    simpa only [d246, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4497 (p : Pattern) (guard : d854 p = 1) : d247 p ≤ (2 : Int) + d898 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d247, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4491 p hg
    simpa only [d247, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d247, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4496 p hg
    simpa only [d247, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4498 (p : Pattern) (guard : d854 p = 1) : d248 p ≤ (2 : Int) + d899 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d248, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d248, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d248, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d248, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4499 (p : Pattern) (guard : d854 p = 1) : d138 p ≤ (2 : Int) + d900 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d138, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d138, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d138, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4488 p hg
    simpa only [d138, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4500 (p : Pattern) (guard : d854 p = 1) : d140 p ≤ (2 : Int) + d901 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d140, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d140, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d140, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d140, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4501 (p : Pattern) (guard : d854 p = 1) : d188 p ≤ (2 : Int) + d902 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d188, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4500 p hg
    simpa only [d188, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d188, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d188, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4502 (p : Pattern) (guard : d854 p = 1) : d145 p ≤ (2 : Int) + d903 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d145, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4453 p hg
    simpa only [d145, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d145, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d145, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4503 (p : Pattern) (guard : d854 p = 1) : d147 p ≤ (2 : Int) + d904 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d147, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4502 p hg
    simpa only [d147, d904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d147, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4494 p hg
    simpa only [d147, d904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4504 (p : Pattern) (guard : d854 p = 1) : d249 p ≤ (2 : Int) + d905 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d249, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4503 p hg
    simpa only [d249, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d249, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d249, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4505 (p : Pattern) (guard : d854 p = 1) : d250 p ≤ (2 : Int) + d906 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d250, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4501 p hg
    simpa only [d250, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d250, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4504 p hg
    simpa only [d250, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4506 (p : Pattern) (guard : d854 p = 1) : d251 p ≤ (2 : Int) + d907 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d251, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d251, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d251, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d251, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4507 (p : Pattern) (guard : d854 p = 1) : d252 p ≤ (2 : Int) + d908 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d252, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4498 p hg
    simpa only [d252, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d252, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4506 p hg
    simpa only [d252, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4508 (p : Pattern) (guard : d854 p = 1) : d191 p ≤ (2 : Int) + d909 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d191, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4490 p hg
    simpa only [d191, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d191, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d191, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4509 (p : Pattern) (guard : d854 p = 1) : d253 p ≤ (2 : Int) + d910 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d253, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4495 p hg
    simpa only [d253, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d253, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d253, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4510 (p : Pattern) (guard : d854 p = 1) : d254 p ≤ (2 : Int) + d911 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d254, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4508 p hg
    simpa only [d254, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d254, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4509 p hg
    simpa only [d254, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4511 (p : Pattern) (guard : d854 p = 1) : d255 p ≤ (2 : Int) + d912 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d255, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4510 p hg
    simpa only [d255, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d255, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d255, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4512 (p : Pattern) (guard : d854 p = 1) : d256 p ≤ (2 : Int) + d913 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d256, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d256, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d256, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d256, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4513 (p : Pattern) (guard : d854 p = 1) : d257 p ≤ (2 : Int) + d914 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d257, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4507 p hg
    simpa only [d257, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d257, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4512 p hg
    simpa only [d257, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4514 (p : Pattern) (guard : d854 p = 1) : d258 p ≤ (2 : Int) + d915 p := by
  cases selected : p 108 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d258, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d258, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d258, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4513 p hg
    simpa only [d258, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4515 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4516 (p : Pattern) (guard : d917 p = 1) : d6 p ≤ (2 : Int) + d0 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4517 (p : Pattern) (guard : d1174 p = 1) : d7 p ≤ (2 : Int) + d0 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2640 p hg
    simpa only [d1174, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1174, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4518 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4519 (p : Pattern) (guard : d917 p = 1) : d54 p ≤ (2 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4520 (p : Pattern) (guard : d1174 p = 1) : d55 p ≤ (2 : Int) + d2 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2644 p hg
    simpa only [d1174, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d1174, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4521 (p : Pattern) (guard : d1174 p = 1) : d56 p ≤ (2 : Int) + d45 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4522 (p : Pattern) (guard : d1174 p = 1) : d57 p ≤ (2 : Int) + d46 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4521 p hg
    simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4523 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (2 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4524 (p : Pattern) (guard : d917 p = 1) : d10 p ≤ (2 : Int) + d8 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4525 (p : Pattern) (guard : d1174 p = 1) : d11 p ≤ (2 : Int) + d8 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2650 p hg
    simpa only [d1174, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4524 p hg
    simpa only [d1174, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4526 (p : Pattern) (guard : d1174 p = 1) : d12 p ≤ (2 : Int) + d1055 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4527 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4528 (p : Pattern) (guard : d917 p = 1) : d59 p ≤ (2 : Int) + d9 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2656 p hg
    simpa only [d917, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4527 p hg
    simpa only [d917, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4529 (p : Pattern) (guard : d1174 p = 1) : d60 p ≤ (2 : Int) + d9 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2655 p hg
    simpa only [d1174, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4528 p hg
    simpa only [d1174, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4530 (p : Pattern) (guard : d1174 p = 1) : d61 p ≤ (2 : Int) + d1056 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4529 p hg
    simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4531 (p : Pattern) (guard : d1174 p = 1) : d62 p ≤ (2 : Int) + d1057 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4521 p hg
    simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4530 p hg
    simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4532 (p : Pattern) (guard : d1174 p = 1) : d63 p ≤ (2 : Int) + d1058 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4533 (p : Pattern) (guard : d1174 p = 1) : d64 p ≤ (2 : Int) + d1059 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4522 p hg
    simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4532 p hg
    simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4534 (p : Pattern) (guard : d1174 p = 1) : d106 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4535 (p : Pattern) (guard : d1174 p = 1) : d119 p ≤ (2 : Int) + d82 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4536 (p : Pattern) (guard : d1174 p = 1) : d120 p ≤ (2 : Int) + d83 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4535 p hg
    simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4537 (p : Pattern) (guard : d1174 p = 1) : d121 p ≤ (2 : Int) + d84 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4536 p hg
    simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4538 (p : Pattern) (guard : d1174 p = 1) : d122 p ≤ (2 : Int) + d85 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4534 p hg
    simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4537 p hg
    simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4539 (p : Pattern) (guard : d1174 p = 1) : d179 p ≤ (2 : Int) + d162 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4534 p hg
    simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4538 p hg
    simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4540 (p : Pattern) (guard : d1174 p = 1) : d65 p ≤ (2 : Int) + d1060 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4529 p hg
    simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4541 (p : Pattern) (guard : d1174 p = 1) : d109 p ≤ (2 : Int) + d1061 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4542 (p : Pattern) (guard : d1174 p = 1) : d125 p ≤ (2 : Int) + d1062 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4529 p hg
    simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4543 (p : Pattern) (guard : d1174 p = 1) : d126 p ≤ (2 : Int) + d1063 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4542 p hg
    simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4544 (p : Pattern) (guard : d1174 p = 1) : d127 p ≤ (2 : Int) + d1064 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4536 p hg
    simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4543 p hg
    simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4545 (p : Pattern) (guard : d1174 p = 1) : d128 p ≤ (2 : Int) + d1065 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4544 p hg
    simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4546 (p : Pattern) (guard : d1174 p = 1) : d129 p ≤ (2 : Int) + d1066 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4545 p hg
    simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4547 (p : Pattern) (guard : d1174 p = 1) : d237 p ≤ (2 : Int) + d1067 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4546 p hg
    simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4548 (p : Pattern) (guard : d1174 p = 1) : d238 p ≤ (2 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4547 p hg
    simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4549 (p : Pattern) (guard : d1174 p = 1) : d239 p ≤ (2 : Int) + d1069 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4548 p hg
    simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4550 (p : Pattern) (guard : d1174 p = 1) : d68 p ≤ (2 : Int) + d48 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4522 p hg
    simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4551 (p : Pattern) (guard : d1174 p = 1) : d69 p ≤ (2 : Int) + d1070 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4532 p hg
    simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4552 (p : Pattern) (guard : d1174 p = 1) : d70 p ≤ (2 : Int) + d1071 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4550 p hg
    simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4553 (p : Pattern) (guard : d1174 p = 1) : d181 p ≤ (2 : Int) + d164 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4538 p hg
    simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4554 (p : Pattern) (guard : d1174 p = 1) : d240 p ≤ (2 : Int) + d1072 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4546 p hg
    simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4555 (p : Pattern) (guard : d1174 p = 1) : d241 p ≤ (2 : Int) + d1073 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4553 p hg
    simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4554 p hg
    simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4556 (p : Pattern) (guard : d1174 p = 1) : d242 p ≤ (2 : Int) + d1074 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4552 p hg
    simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4555 p hg
    simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4557 (p : Pattern) (guard : d1174 p = 1) : d243 p ≤ (2 : Int) + d1075 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4558 (p : Pattern) (guard : d1174 p = 1) : d66 p ≤ (2 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4559 (p : Pattern) (guard : d1174 p = 1) : d244 p ≤ (2 : Int) + d1077 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4560 (p : Pattern) (guard : d1174 p = 1) : d245 p ≤ (2 : Int) + d1078 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4557 p hg
    simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4559 p hg
    simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4561 (p : Pattern) (guard : d1174 p = 1) : d137 p ≤ (2 : Int) + d92 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4535 p hg
    simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4562 (p : Pattern) (guard : d1174 p = 1) : d139 p ≤ (2 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4536 p hg
    simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4561 p hg
    simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4563 (p : Pattern) (guard : d1174 p = 1) : d153 p ≤ (2 : Int) + d100 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4522 p hg
    simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4562 p hg
    simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4564 (p : Pattern) (guard : d1174 p = 1) : d186 p ≤ (2 : Int) + d169 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4522 p hg
    simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4563 p hg
    simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4565 (p : Pattern) (guard : d1174 p = 1) : d143 p ≤ (2 : Int) + d1079 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4542 p hg
    simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4529 p hg
    simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4566 (p : Pattern) (guard : d1174 p = 1) : d144 p ≤ (2 : Int) + d1080 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4561 p hg
    simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4565 p hg
    simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4567 (p : Pattern) (guard : d1174 p = 1) : d146 p ≤ (2 : Int) + d1081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4544 p hg
    simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4566 p hg
    simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4568 (p : Pattern) (guard : d1174 p = 1) : d155 p ≤ (2 : Int) + d1082 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4532 p hg
    simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4567 p hg
    simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4569 (p : Pattern) (guard : d1174 p = 1) : d246 p ≤ (2 : Int) + d1083 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4532 p hg
    simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4570 (p : Pattern) (guard : d1174 p = 1) : d247 p ≤ (2 : Int) + d1084 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4569 p hg
    simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4571 (p : Pattern) (guard : d1174 p = 1) : d248 p ≤ (2 : Int) + d1085 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4570 p hg
    simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4572 (p : Pattern) (guard : d1174 p = 1) : d138 p ≤ (2 : Int) + d93 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4561 p hg
    simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4573 (p : Pattern) (guard : d1174 p = 1) : d140 p ≤ (2 : Int) + d95 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4572 p hg
    simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4562 p hg
    simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4574 (p : Pattern) (guard : d1174 p = 1) : d188 p ≤ (2 : Int) + d171 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4573 p hg
    simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4575 (p : Pattern) (guard : d1174 p = 1) : d145 p ≤ (2 : Int) + d1086 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4566 p hg
    simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4576 (p : Pattern) (guard : d1174 p = 1) : d147 p ≤ (2 : Int) + d1087 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4575 p hg
    simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4567 p hg
    simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4577 (p : Pattern) (guard : d1174 p = 1) : d249 p ≤ (2 : Int) + d1088 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4576 p hg
    simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4578 (p : Pattern) (guard : d1174 p = 1) : d250 p ≤ (2 : Int) + d1089 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4574 p hg
    simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4577 p hg
    simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4579 (p : Pattern) (guard : d1174 p = 1) : d251 p ≤ (2 : Int) + d1090 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4578 p hg
    simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4580 (p : Pattern) (guard : d1174 p = 1) : d252 p ≤ (2 : Int) + d1091 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4571 p hg
    simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4579 p hg
    simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4581 (p : Pattern) (guard : d1174 p = 1) : d191 p ≤ (2 : Int) + d174 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4563 p hg
    simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4582 (p : Pattern) (guard : d1174 p = 1) : d253 p ≤ (2 : Int) + d1092 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4583 (p : Pattern) (guard : d1174 p = 1) : d254 p ≤ (2 : Int) + d1093 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4581 p hg
    simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4582 p hg
    simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4584 (p : Pattern) (guard : d1174 p = 1) : d255 p ≤ (2 : Int) + d1094 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4583 p hg
    simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4585 (p : Pattern) (guard : d1174 p = 1) : d256 p ≤ (2 : Int) + d1095 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4584 p hg
    simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4586 (p : Pattern) (guard : d1174 p = 1) : d257 p ≤ (2 : Int) + d1096 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4580 p hg
    simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4587 (p : Pattern) (guard : d1174 p = 1) : d258 p ≤ (2 : Int) + d1097 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4560 p hg
    simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4586 p hg
    simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4588 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4589 (p : Pattern) (guard : d854 p = 1) : d24 p ≤ (0 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4588 p hg
    simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4590 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4591 (p : Pattern) (guard : d854 p = 1) : d525 p ≤ (0 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4590 p hg
    simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4592 (p : Pattern) (guard : d854 p = 1) : d526 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4593 (p : Pattern) (guard : d854 p = 1) : d527 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4592 p hg
    simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4594 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4595 (p : Pattern) (guard : d854 p = 1) : d25 p ≤ (0 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4594 p hg
    simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4596 (p : Pattern) (guard : d854 p = 1) : d26 p ≤ (0 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4597 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4598 (p : Pattern) (guard : d854 p = 1) : d528 p ≤ (0 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4597 p hg
    simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4599 (p : Pattern) (guard : d854 p = 1) : d529 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4598 p hg
    simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4600 (p : Pattern) (guard : d854 p = 1) : d530 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4592 p hg
    simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4599 p hg
    simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4601 (p : Pattern) (guard : d854 p = 1) : d531 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4596 p hg
    simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4600 p hg
    simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4602 (p : Pattern) (guard : d854 p = 1) : d532 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4593 p hg
    simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4601 p hg
    simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4603 (p : Pattern) (guard : d854 p = 1) : d533 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4604 (p : Pattern) (guard : d854 p = 1) : d534 p ≤ (0 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4605 (p : Pattern) (guard : d854 p = 1) : d535 p ≤ (0 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4604 p hg
    simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4606 (p : Pattern) (guard : d854 p = 1) : d536 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4605 p hg
    simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4607 (p : Pattern) (guard : d854 p = 1) : d537 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4603 p hg
    simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4606 p hg
    simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4608 (p : Pattern) (guard : d854 p = 1) : d538 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4603 p hg
    simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4607 p hg
    simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4609 (p : Pattern) (guard : d854 p = 1) : d539 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4598 p hg
    simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4610 (p : Pattern) (guard : d854 p = 1) : d540 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4596 p hg
    simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4611 (p : Pattern) (guard : d854 p = 1) : d541 p ≤ (0 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4598 p hg
    simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4612 (p : Pattern) (guard : d854 p = 1) : d542 p ≤ (0 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4611 p hg
    simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4613 (p : Pattern) (guard : d854 p = 1) : d543 p ≤ (0 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4605 p hg
    simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4612 p hg
    simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4614 (p : Pattern) (guard : d854 p = 1) : d544 p ≤ (0 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4613 p hg
    simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4615 (p : Pattern) (guard : d854 p = 1) : d545 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4610 p hg
    simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4614 p hg
    simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4616 (p : Pattern) (guard : d854 p = 1) : d546 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4610 p hg
    simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4615 p hg
    simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4617 (p : Pattern) (guard : d854 p = 1) : d547 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4608 p hg
    simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4616 p hg
    simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4618 (p : Pattern) (guard : d854 p = 1) : d548 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4602 p hg
    simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4617 p hg
    simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4619 (p : Pattern) (guard : d854 p = 1) : d549 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4593 p hg
    simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
