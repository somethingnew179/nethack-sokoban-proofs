/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons158
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c22260 (pattern : Twelve) (guard : d1 pattern = 1) : d133 pattern ≤ (19 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22256 pattern childGuard
    simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22259 pattern childGuard
    simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22261 (pattern : Twelve) (guard : d1 pattern = 1) : d142 pattern ≤ (19 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22152 pattern childGuard
    simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22260 pattern childGuard
    simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22262 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (19 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22253 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22254 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22263 (pattern : Twelve) (guard : d1 pattern = 1) : d126 pattern ≤ (19 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22117 pattern childGuard
    simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22262 pattern childGuard
    simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22264 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (19 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22248 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22265 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (19 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22263 pattern childGuard
    simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22264 pattern childGuard
    simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22266 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (19 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22128 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22124 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22267 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22112 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22268 (pattern : Twelve) (guard : d1 pattern = 1) : d135 pattern ≤ (19 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22266 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22267 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22269 (pattern : Twelve) (guard : d1 pattern = 1) : d143 pattern ≤ (19 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22265 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22268 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22270 (pattern : Twelve) (guard : d1 pattern = 1) : d148 pattern ≤ (19 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22261 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22269 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22271 (pattern : Twelve) (guard : d1 pattern = 1) : d151 pattern ≤ (19 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22252 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22270 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22272 (pattern : Twelve) (guard : d1 pattern = 1) : d152 pattern ≤ (19 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22240 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22273 (pattern : Twelve) (guard : d1 pattern = 1) : d154 pattern ≤ (19 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22271 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22272 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22274 (pattern : Twelve) (guard : d1 pattern = 1) : d155 pattern ≤ (19 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22242 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22273 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22275 (pattern : Twelve) (guard : d1 pattern = 1) : d778 pattern ≤ (19 : Int) + d779 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22117 pattern childGuard
    simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22146 pattern childGuard
    simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22276 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (19 : Int) + d1247 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22159 pattern childGuard
    simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22146 pattern childGuard
    simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22277 (pattern : Twelve) (guard : d1 pattern = 1) : d782 pattern ≤ (19 : Int) + d1249 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22275 pattern childGuard
    simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22276 pattern childGuard
    simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22278 (pattern : Twelve) (guard : d1 pattern = 1) : d788 pattern ≤ (19 : Int) + d1253 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22115 pattern childGuard
    simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22277 pattern childGuard
    simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22279 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (19 : Int) + d1248 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22117 pattern childGuard
    simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22153 pattern childGuard
    simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22280 (pattern : Twelve) (guard : d1 pattern = 1) : d789 pattern ≤ (19 : Int) + d1254 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22279 pattern childGuard
    simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22173 pattern childGuard
    simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22281 (pattern : Twelve) (guard : d1 pattern = 1) : d794 pattern ≤ (19 : Int) + d1258 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22278 pattern childGuard
    simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22280 pattern childGuard
    simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22282 (pattern : Twelve) (guard : d1 pattern = 1) : d783 pattern ≤ (19 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22205 pattern childGuard
    simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22186 pattern childGuard
    simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22283 (pattern : Twelve) (guard : d1 pattern = 1) : d790 pattern ≤ (19 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22282 pattern childGuard
    simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22210 pattern childGuard
    simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22284 (pattern : Twelve) (guard : d1 pattern = 1) : d795 pattern ≤ (19 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22283 pattern childGuard
    simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22216 pattern childGuard
    simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22285 (pattern : Twelve) (guard : d1 pattern = 1) : d798 pattern ≤ (19 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22281 pattern childGuard
    simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22284 pattern childGuard
    simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22286 (pattern : Twelve) (guard : d1 pattern = 1) : d799 pattern ≤ (19 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22281 pattern childGuard
    simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22217 pattern childGuard
    simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22287 (pattern : Twelve) (guard : d1 pattern = 1) : d802 pattern ≤ (19 : Int) + d1261 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22285 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22286 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22288 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (19 : Int) + d780 pattern := by
  omega
theorem c22289 (pattern : Twelve) (guard : d1 pattern = 1) : d784 pattern ≤ (19 : Int) + d1250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22157 pattern childGuard
    simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22288 pattern childGuard
    simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22290 (pattern : Twelve) (guard : d1 pattern = 1) : d791 pattern ≤ (19 : Int) + d1255 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22205 pattern childGuard
    simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22289 pattern childGuard
    simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22291 (pattern : Twelve) (guard : d1 pattern = 1) : d796 pattern ≤ (19 : Int) + d1259 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22290 pattern childGuard
    simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22216 pattern childGuard
    simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22292 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (19 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22156 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22293 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (19 : Int) + d781 pattern := by
  omega
theorem c22294 (pattern : Twelve) (guard : d1 pattern = 1) : d785 pattern ≤ (19 : Int) + d1251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22292 pattern childGuard
    simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22293 pattern childGuard
    simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22295 (pattern : Twelve) (guard : d1 pattern = 1) : d792 pattern ≤ (19 : Int) + d1256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22212 pattern childGuard
    simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22294 pattern childGuard
    simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22296 (pattern : Twelve) (guard : d1 pattern = 1) : d786 pattern ≤ (19 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22292 pattern childGuard
    simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22297 (pattern : Twelve) (guard : d1 pattern = 1) : d787 pattern ≤ (19 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22214 pattern childGuard
    simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22298 (pattern : Twelve) (guard : d1 pattern = 1) : d793 pattern ≤ (19 : Int) + d1257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22296 pattern childGuard
    simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22297 pattern childGuard
    simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22299 (pattern : Twelve) (guard : d1 pattern = 1) : d797 pattern ≤ (19 : Int) + d1260 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22295 pattern childGuard
    simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22298 pattern childGuard
    simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22300 (pattern : Twelve) (guard : d1 pattern = 1) : d800 pattern ≤ (19 : Int) + d1262 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22291 pattern childGuard
    simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22299 pattern childGuard
    simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22301 (pattern : Twelve) (guard : d1 pattern = 1) : d801 pattern ≤ (19 : Int) + d1263 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22217 pattern childGuard
    simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22302 (pattern : Twelve) (guard : d1 pattern = 1) : d803 pattern ≤ (19 : Int) + d1264 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22300 pattern childGuard
    simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22301 pattern childGuard
    simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22303 (pattern : Twelve) (guard : d1 pattern = 1) : d804 pattern ≤ (19 : Int) + d1265 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22287 pattern childGuard
    simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22302 pattern childGuard
    simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22304 (pattern : Twelve) (guard : d1 pattern = 1) : d805 pattern ≤ (19 : Int) + d1266 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22274 pattern childGuard
    simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22303 pattern childGuard
    simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22305 (pattern : Twelve) (guard : d1 pattern = 1) : d806 pattern ≤ (19 : Int) + d1267 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22222 pattern childGuard
    simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22304 pattern childGuard
    simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22306 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (19 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22075 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22090 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22307 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (19 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22076 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22306 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22308 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (19 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22307 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22224 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22309 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (19 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22080 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22223 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22310 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (19 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22309 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22224 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22311 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (19 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22308 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22310 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22312 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (19 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22077 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22311 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22313 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d6 pattern := by
  change (0 : Int) ≤ (19 : Int) + 6
  decide
theorem c22314 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d6 pattern := by
  change (2 : Int) ≤ (19 : Int) + 6
  decide
theorem c22315 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22313 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22314 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22316 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (19 : Int) + d6 pattern := by
  change (1 : Int) ≤ (19 : Int) + 6
  decide
theorem c22317 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22316 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22107 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22318 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22315 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22317 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22319 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22314 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22110 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22320 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22319 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22109 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22321 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22318 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22320 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22322 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22320 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22323 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22321 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22322 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22324 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (19 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22089 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22323 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22325 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (19 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22312 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22324 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22326 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (19 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22093 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22246 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22327 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (19 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22116 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22326 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22328 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (19 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22307 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22327 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22329 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (19 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22309 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22330 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (19 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22328 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22329 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22331 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (19 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22141 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22330 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22332 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (19 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22089 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22333 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (19 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22129 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22332 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22334 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (19 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22333 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22323 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22335 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (19 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22331 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22334 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22336 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (19 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22325 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22335 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22337 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (19 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22309 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22248 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22338 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (19 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22328 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22337 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22339 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (19 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22118 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22338 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22340 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (19 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22129 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22323 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22341 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (19 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22339 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22340 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22342 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (19 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22155 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22166 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22343 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (19 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22327 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22342 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22344 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (19 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22158 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22247 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22345 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (19 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22344 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22346 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (19 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22343 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22345 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22347 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (19 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22164 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22346 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22348 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (19 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22168 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22188 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22349 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22320 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22120 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22350 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22120 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22351 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22349 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22350 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22352 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (19 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22348 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22351 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22353 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (19 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22347 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22352 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22354 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (19 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22341 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22353 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22355 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (19 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22335 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22356 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (19 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22354 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22355 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22357 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (19 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22336 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22356 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22358 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (19 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22089 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22117 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22359 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (19 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22358 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22323 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22360 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (19 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22312 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22359 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22361 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (19 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22224 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22362 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (19 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22328 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22361 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22363 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (19 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22141 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22362 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22364 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (19 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22129 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22163 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22365 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (19 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22364 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22323 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22366 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (19 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22363 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22365 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22367 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (19 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22360 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22366 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22368 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (19 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22224 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22248 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22369 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (19 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22328 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22368 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22370 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (19 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22118 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22369 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22371 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (19 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22129 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22157 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22372 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (19 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22371 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22323 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22373 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (19 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22370 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22372 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22374 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (19 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22343 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22264 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22375 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (19 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22164 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22374 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22376 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (19 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22168 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22292 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22377 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (19 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22376 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22351 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22378 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (19 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22375 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22377 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22379 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (19 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22373 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22378 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22380 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (19 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22366 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22381 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (19 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22379 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22380 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22382 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (19 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22367 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22381 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22383 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (19 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22357 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22382 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22384 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (19 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22078 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22087 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22385 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (19 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22384 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22092 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22386 (pattern : Twelve) (guard : d1 pattern = 1) : d874 pattern ≤ (19 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22307 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22385 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22387 (pattern : Twelve) (guard : d1 pattern = 1) : d875 pattern ≤ (19 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22309 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22385 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22388 (pattern : Twelve) (guard : d1 pattern = 1) : d882 pattern ≤ (19 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22386 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22387 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22389 (pattern : Twelve) (guard : d1 pattern = 1) : d890 pattern ≤ (19 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22077 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22388 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22390 (pattern : Twelve) (guard : d1 pattern = 1) : d876 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22318 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22120 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22391 (pattern : Twelve) (guard : d1 pattern = 1) : d883 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22390 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22322 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22392 (pattern : Twelve) (guard : d1 pattern = 1) : d891 pattern ≤ (19 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22089 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22391 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22393 (pattern : Twelve) (guard : d1 pattern = 1) : d898 pattern ≤ (19 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22389 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22392 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22394 (pattern : Twelve) (guard : d1 pattern = 1) : d877 pattern ≤ (19 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22307 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22344 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22395 (pattern : Twelve) (guard : d1 pattern = 1) : d884 pattern ≤ (19 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22394 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22329 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22396 (pattern : Twelve) (guard : d1 pattern = 1) : d892 pattern ≤ (19 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22141 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22395 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22397 (pattern : Twelve) (guard : d1 pattern = 1) : d893 pattern ≤ (19 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22333 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22391 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22398 (pattern : Twelve) (guard : d1 pattern = 1) : d899 pattern ≤ (19 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22396 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22397 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22399 (pattern : Twelve) (guard : d1 pattern = 1) : d902 pattern ≤ (19 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22393 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22398 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
