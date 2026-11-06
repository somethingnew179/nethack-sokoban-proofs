/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons05
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c960 (pattern : Ten) (guard : d404 pattern = 1) : d207 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d404, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d404, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d404, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c959 pattern childGuard
    simpa only [d404, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c961 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d336 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c962 (pattern : Ten) (guard : d405 pattern = 1) : d290 pattern ≤ (0 : Int) + d338 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d404 pattern = 1 := by simpa only [d405, d290, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c960 pattern childGuard
    simpa only [d405, d290, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d405, d290, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c961 pattern childGuard
    simpa only [d405, d290, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c963 (pattern : Ten) (guard : d404 pattern = 1) : d209 pattern ≤ (0 : Int) + d213 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d404, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d404, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d404, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c939 pattern childGuard
    simpa only [d404, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c964 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d337 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c965 (pattern : Ten) (guard : d405 pattern = 1) : d209 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d404 pattern = 1 := by simpa only [d405, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c963 pattern childGuard
    simpa only [d405, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d405, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c964 pattern childGuard
    simpa only [d405, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c966 (pattern : Ten) (guard : d405 pattern = 1) : d291 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d405 pattern = 1 := by simpa only [d291, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c962 pattern childGuard
    simpa only [d291, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d405 pattern = 1 := by simpa only [d291, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c965 pattern childGuard
    simpa only [d291, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c967 (pattern : Ten) (guard : d368 pattern = 1) : d56 pattern ≤ (0 : Int) + d65 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d368, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c68 pattern childGuard
    simpa only [d368, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d368, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c909 pattern childGuard
    simpa only [d368, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c968 (pattern : Ten) (guard : d369 pattern = 1) : d135 pattern ≤ (0 : Int) + d66 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d367 pattern = 1 := by simpa only [d369, d135, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c908 pattern childGuard
    simpa only [d369, d135, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d368 pattern = 1 := by simpa only [d369, d135, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c967 pattern childGuard
    simpa only [d369, d135, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c969 (pattern : Ten) (guard : d370 pattern = 1) : d209 pattern ≤ (0 : Int) + d219 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d370, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c275 pattern childGuard
    simpa only [d370, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d370, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c914 pattern childGuard
    simpa only [d370, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c970 (pattern : Ten) (guard : d371 pattern = 1) : d291 pattern ≤ (0 : Int) + d220 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d366 pattern = 1 := by simpa only [d371, d291, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c931 pattern childGuard
    simpa only [d371, d291, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d370 pattern = 1 := by simpa only [d371, d291, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c969 pattern childGuard
    simpa only [d371, d291, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c971 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c972 (pattern : Ten) (guard : d350 pattern = 1) : d292 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c971 pattern childGuard
    simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c973 (pattern : Ten) (guard : d350 pattern = 1) : d293 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d293, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c972 pattern childGuard
    simpa only [d293, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d293, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c294 pattern childGuard
    simpa only [d293, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c974 (pattern : Ten) (guard : d350 pattern = 1) : d294 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d294, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c973 pattern childGuard
    simpa only [d294, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d294, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c296 pattern childGuard
    simpa only [d294, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c975 (pattern : Ten) (guard : d350 pattern = 1) : d295 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d295, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c974 pattern childGuard
    simpa only [d295, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d295, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c298 pattern childGuard
    simpa only [d295, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c976 (pattern : Ten) (guard : d350 pattern = 1) : d296 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c975 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c300 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c977 (pattern : Ten) (guard : d350 pattern = 1) : d297 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c976 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c300 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c978 (pattern : Ten) (guard : d350 pattern = 1) : d298 pattern ≤ (0 : Int) + d218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d298, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c977 pattern childGuard
    simpa only [d298, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d298, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c316 pattern childGuard
    simpa only [d298, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c979 (pattern : Ten) (guard : d350 pattern = 1) : d209 pattern ≤ (0 : Int) + d216 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c318 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c940 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c980 (pattern : Ten) (guard : d350 pattern = 1) : d299 pattern ≤ (0 : Int) + d219 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d299, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c979 pattern childGuard
    simpa only [d299, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d299, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d299, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c981 (pattern : Ten) (guard : d350 pattern = 1) : d300 pattern ≤ (0 : Int) + d220 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d300, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c978 pattern childGuard
    simpa only [d300, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d300, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c980 pattern childGuard
    simpa only [d300, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c982 (pattern : Ten) (guard : d350 pattern = 1) : d296 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d296, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c975 pattern childGuard
    simpa only [d296, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d296, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c959 pattern childGuard
    simpa only [d296, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c983 (pattern : Ten) (guard : d350 pattern = 1) : d207 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c300 pattern childGuard
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c959 pattern childGuard
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c984 (pattern : Ten) (guard : d350 pattern = 1) : d297 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c982 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c983 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c985 (pattern : Ten) (guard : d350 pattern = 1) : d211 pattern ≤ (0 : Int) + d333 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d211, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c959 pattern childGuard
    simpa only [d211, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d211, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d211, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c986 (pattern : Ten) (guard : d350 pattern = 1) : d199 pattern ≤ (0 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d199, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c947 pattern childGuard
    simpa only [d199, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d199, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c951 pattern childGuard
    simpa only [d199, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c987 (pattern : Ten) (guard : d350 pattern = 1) : d204 pattern ≤ (0 : Int) + d323 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d204, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c986 pattern childGuard
    simpa only [d204, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d204, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c957 pattern childGuard
    simpa only [d204, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c988 (pattern : Ten) (guard : d350 pattern = 1) : d208 pattern ≤ (0 : Int) + d325 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d208, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c987 pattern childGuard
    simpa only [d208, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d208, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c938 pattern childGuard
    simpa only [d208, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c989 (pattern : Ten) (guard : d350 pattern = 1) : d212 pattern ≤ (0 : Int) + d334 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d212, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c988 pattern childGuard
    simpa only [d212, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d212, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d212, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c990 (pattern : Ten) (guard : d350 pattern = 1) : d215 pattern ≤ (0 : Int) + d336 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d215, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c985 pattern childGuard
    simpa only [d215, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d215, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c989 pattern childGuard
    simpa only [d215, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c991 (pattern : Ten) (guard : d350 pattern = 1) : d298 pattern ≤ (0 : Int) + d338 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d298, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c984 pattern childGuard
    simpa only [d298, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d298, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c990 pattern childGuard
    simpa only [d298, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c992 (pattern : Ten) (guard : d350 pattern = 1) : d214 pattern ≤ (0 : Int) + d335 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d214, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c939 pattern childGuard
    simpa only [d214, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d214, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d214, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c993 (pattern : Ten) (guard : d350 pattern = 1) : d217 pattern ≤ (0 : Int) + d337 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d217, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c992 pattern childGuard
    simpa only [d217, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d217, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d217, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c994 (pattern : Ten) (guard : d350 pattern = 1) : d299 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d299, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c940 pattern childGuard
    simpa only [d299, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d299, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c993 pattern childGuard
    simpa only [d299, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c995 (pattern : Ten) (guard : d350 pattern = 1) : d300 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d300, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c991 pattern childGuard
    simpa only [d300, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d300, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c994 pattern childGuard
    simpa only [d300, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c996 (pattern : Ten) (guard : d367 pattern = 1) : d298 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d367, d298, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c977 pattern childGuard
    simpa only [d367, d298, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d367, d298, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c219 pattern childGuard
    simpa only [d367, d298, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c997 (pattern : Ten) (guard : d367 pattern = 1) : d299 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d367, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c318 pattern childGuard
    simpa only [d367, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d367, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c221 pattern childGuard
    simpa only [d367, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c998 (pattern : Ten) (guard : d367 pattern = 1) : d300 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d367 pattern = 1 := by simpa only [d300, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c996 pattern childGuard
    simpa only [d300, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d367 pattern = 1 := by simpa only [d300, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c997 pattern childGuard
    simpa only [d300, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c999 (pattern : Ten) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1000 (pattern : Ten) (guard : d395 pattern = 1) : d58 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c999 pattern childGuard
    simpa only [d395, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1001 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (0 : Int) + d55 pattern := by
  omega
theorem c1002 (pattern : Ten) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1003 (pattern : Ten) (guard : d395 pattern = 1) : d59 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1001 pattern childGuard
    simpa only [d395, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1002 pattern childGuard
    simpa only [d395, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1004 (pattern : Ten) (guard : d395 pattern = 1) : d62 pattern ≤ (0 : Int) + d152 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d62, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1000 pattern childGuard
    simpa only [d62, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d62, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1003 pattern childGuard
    simpa only [d62, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1005 (pattern : Ten) (guard : d395 pattern = 1) : d64 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c885 pattern childGuard
    simpa only [d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1004 pattern childGuard
    simpa only [d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1006 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1007 (pattern : Ten) (guard : d395 pattern = 1) : d60 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c331 pattern childGuard
    simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1006 pattern childGuard
    simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1008 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (0 : Int) + d57 pattern := by
  omega
theorem c1009 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1010 (pattern : Ten) (guard : d395 pattern = 1) : d61 pattern ≤ (0 : Int) + d57 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1008 pattern childGuard
    simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1009 pattern childGuard
    simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1011 (pattern : Ten) (guard : d395 pattern = 1) : d63 pattern ≤ (0 : Int) + d153 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d63, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1007 pattern childGuard
    simpa only [d63, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d63, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1010 pattern childGuard
    simpa only [d63, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1012 (pattern : Ten) (guard : d395 pattern = 1) : d65 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d65, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c919 pattern childGuard
    simpa only [d65, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d65, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1011 pattern childGuard
    simpa only [d65, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1013 (pattern : Ten) (guard : d395 pattern = 1) : d66 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d66, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1005 pattern childGuard
    simpa only [d66, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d66, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1012 pattern childGuard
    simpa only [d66, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1014 (pattern : Ten) (guard : d395 pattern = 1) : d296 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d296, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c975 pattern childGuard
    simpa only [d395, d296, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d296, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c75 pattern childGuard
    simpa only [d395, d296, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1015 (pattern : Ten) (guard : d395 pattern = 1) : d207 pattern ≤ (0 : Int) + d207 pattern := by
  omega
theorem c1016 (pattern : Ten) (guard : d395 pattern = 1) : d297 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d297, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1014 pattern childGuard
    simpa only [d297, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d297, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1015 pattern childGuard
    simpa only [d297, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1017 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1018 (pattern : Ten) (guard : d395 pattern = 1) : d211 pattern ≤ (0 : Int) + d324 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c959 pattern childGuard
    simpa only [d395, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1017 pattern childGuard
    simpa only [d395, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1019 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d325 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1020 (pattern : Ten) (guard : d395 pattern = 1) : d212 pattern ≤ (0 : Int) + d325 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c988 pattern childGuard
    simpa only [d395, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1019 pattern childGuard
    simpa only [d395, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1021 (pattern : Ten) (guard : d395 pattern = 1) : d215 pattern ≤ (0 : Int) + d327 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d215, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1018 pattern childGuard
    simpa only [d215, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d215, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1020 pattern childGuard
    simpa only [d215, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1022 (pattern : Ten) (guard : d395 pattern = 1) : d298 pattern ≤ (0 : Int) + d329 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d298, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1016 pattern childGuard
    simpa only [d298, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d298, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1021 pattern childGuard
    simpa only [d298, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1023 (pattern : Ten) (guard : d395 pattern = 1) : d209 pattern ≤ (0 : Int) + d209 pattern := by
  omega
theorem c1024 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d210 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1025 (pattern : Ten) (guard : d395 pattern = 1) : d214 pattern ≤ (0 : Int) + d210 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c939 pattern childGuard
    simpa only [d395, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1024 pattern childGuard
    simpa only [d395, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1026 (pattern : Ten) (guard : d395 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c1027 (pattern : Ten) (guard : d395 pattern = 1) : d217 pattern ≤ (0 : Int) + d328 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d217, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1025 pattern childGuard
    simpa only [d217, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d217, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1026 pattern childGuard
    simpa only [d217, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1028 (pattern : Ten) (guard : d395 pattern = 1) : d299 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d299, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1023 pattern childGuard
    simpa only [d299, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d299, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1027 pattern childGuard
    simpa only [d299, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1029 (pattern : Ten) (guard : d395 pattern = 1) : d300 pattern ≤ (0 : Int) + d331 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d300, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1022 pattern childGuard
    simpa only [d300, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d300, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1028 pattern childGuard
    simpa only [d300, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1030 (pattern : Ten) (guard : d354 pattern = 1) : d297 pattern ≤ (0 : Int) + d235 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d297, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c976 pattern childGuard
    simpa only [d354, d297, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d297, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c75 pattern childGuard
    simpa only [d354, d297, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1031 (pattern : Ten) (guard : d354 pattern = 1) : d215 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c303 pattern childGuard
    simpa only [d354, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d354, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1032 (pattern : Ten) (guard : d354 pattern = 1) : d298 pattern ≤ (0 : Int) + d236 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d298, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1030 pattern childGuard
    simpa only [d298, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d298, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1031 pattern childGuard
    simpa only [d298, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1033 (pattern : Ten) (guard : d354 pattern = 1) : d217 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c307 pattern childGuard
    simpa only [d354, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c85 pattern childGuard
    simpa only [d354, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1034 (pattern : Ten) (guard : d354 pattern = 1) : d299 pattern ≤ (0 : Int) + d237 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d299, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c306 pattern childGuard
    simpa only [d299, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d299, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1033 pattern childGuard
    simpa only [d299, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1035 (pattern : Ten) (guard : d354 pattern = 1) : d300 pattern ≤ (0 : Int) + d238 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d300, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1032 pattern childGuard
    simpa only [d300, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d300, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1034 pattern childGuard
    simpa only [d300, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1036 (pattern : Ten) (guard : d0 pattern = 1) : d137 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1037 (pattern : Ten) (guard : d384 pattern = 1) : d138 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d138, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d138, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d138, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1036 pattern childGuard
    simpa only [d384, d138, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1038 (pattern : Ten) (guard : d384 pattern = 1) : d139 pattern ≤ (0 : Int) + d87 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d139, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1037 pattern childGuard
    simpa only [d139, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d139, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c396 pattern childGuard
    simpa only [d139, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1039 (pattern : Ten) (guard : d384 pattern = 1) : d142 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d142, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1038 pattern childGuard
    simpa only [d142, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d142, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c399 pattern childGuard
    simpa only [d142, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1040 (pattern : Ten) (guard : d384 pattern = 1) : d140 pattern ≤ (0 : Int) + d89 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d140, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c396 pattern childGuard
    simpa only [d140, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d140, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c405 pattern childGuard
    simpa only [d140, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1041 (pattern : Ten) (guard : d384 pattern = 1) : d143 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d143, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1040 pattern childGuard
    simpa only [d143, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d143, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c407 pattern childGuard
    simpa only [d143, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1042 (pattern : Ten) (guard : d384 pattern = 1) : d145 pattern ≤ (0 : Int) + d99 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d145, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1039 pattern childGuard
    simpa only [d145, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d145, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1041 pattern childGuard
    simpa only [d145, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1043 (pattern : Ten) (guard : d384 pattern = 1) : d141 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d141, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c396 pattern childGuard
    simpa only [d141, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d141, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c414 pattern childGuard
    simpa only [d141, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1044 (pattern : Ten) (guard : d384 pattern = 1) : d144 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d144, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1043 pattern childGuard
    simpa only [d144, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d144, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c416 pattern childGuard
    simpa only [d144, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1045 (pattern : Ten) (guard : d384 pattern = 1) : d146 pattern ≤ (0 : Int) + d100 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d146, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1044 pattern childGuard
    simpa only [d146, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d146, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1041 pattern childGuard
    simpa only [d146, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1046 (pattern : Ten) (guard : d384 pattern = 1) : d147 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d147, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1042 pattern childGuard
    simpa only [d147, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d147, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1045 pattern childGuard
    simpa only [d147, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1047 (pattern : Ten) (guard : d384 pattern = 1) : d148 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d148, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1046 pattern childGuard
    simpa only [d148, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d148, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c425 pattern childGuard
    simpa only [d148, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1048 (pattern : Ten) (guard : d384 pattern = 1) : d149 pattern ≤ (0 : Int) + d107 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d149, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1047 pattern childGuard
    simpa only [d149, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d149, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c427 pattern childGuard
    simpa only [d149, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1049 (pattern : Ten) (guard : d383 pattern = 1) : d173 pattern ≤ (0 : Int) + d249 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c481 pattern childGuard
    simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c432 pattern childGuard
    simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1050 (pattern : Ten) (guard : d383 pattern = 1) : d302 pattern ≤ (0 : Int) + d253 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d302, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1049 pattern childGuard
    simpa only [d302, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d302, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c435 pattern childGuard
    simpa only [d302, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1051 (pattern : Ten) (guard : d383 pattern = 1) : d304 pattern ≤ (0 : Int) + d257 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d304, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1050 pattern childGuard
    simpa only [d304, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d304, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c437 pattern childGuard
    simpa only [d304, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1052 (pattern : Ten) (guard : d383 pattern = 1) : d301 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d301, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c432 pattern childGuard
    simpa only [d301, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d301, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c443 pattern childGuard
    simpa only [d301, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1053 (pattern : Ten) (guard : d383 pattern = 1) : d303 pattern ≤ (0 : Int) + d255 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d303, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1052 pattern childGuard
    simpa only [d303, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d303, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d303, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1054 (pattern : Ten) (guard : d383 pattern = 1) : d305 pattern ≤ (0 : Int) + d258 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d305, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1053 pattern childGuard
    simpa only [d305, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d305, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c437 pattern childGuard
    simpa only [d305, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1055 (pattern : Ten) (guard : d383 pattern = 1) : d306 pattern ≤ (0 : Int) + d261 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d306, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1051 pattern childGuard
    simpa only [d306, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d306, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1054 pattern childGuard
    simpa only [d306, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1056 (pattern : Ten) (guard : d383 pattern = 1) : d307 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d307, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1055 pattern childGuard
    simpa only [d307, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d307, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c452 pattern childGuard
    simpa only [d307, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1057 (pattern : Ten) (guard : d383 pattern = 1) : d308 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d308, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1056 pattern childGuard
    simpa only [d308, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d308, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c454 pattern childGuard
    simpa only [d308, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1058 (pattern : Ten) (guard : d0 pattern = 1) : d137 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1059 (pattern : Ten) (guard : d384 pattern = 1) : d138 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d138, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d138, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d138, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1058 pattern childGuard
    simpa only [d384, d138, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1060 (pattern : Ten) (guard : d0 pattern = 1) : d12 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1061 (pattern : Ten) (guard : d387 pattern = 1) : d139 pattern ≤ (0 : Int) + d108 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d139, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1059 pattern childGuard
    simpa only [d387, d139, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d139, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1060 pattern childGuard
    simpa only [d387, d139, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1062 (pattern : Ten) (guard : d384 pattern = 1) : d12 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c413 pattern childGuard
    simpa only [d384, d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1063 (pattern : Ten) (guard : d387 pattern = 1) : d18 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1062 pattern childGuard
    simpa only [d387, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c505 pattern childGuard
    simpa only [d387, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1064 (pattern : Ten) (guard : d387 pattern = 1) : d142 pattern ≤ (0 : Int) + d109 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d142, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1061 pattern childGuard
    simpa only [d142, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d142, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1063 pattern childGuard
    simpa only [d142, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1065 (pattern : Ten) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1066 (pattern : Ten) (guard : d387 pattern = 1) : d140 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1062 pattern childGuard
    simpa only [d387, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1065 pattern childGuard
    simpa only [d387, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1067 (pattern : Ten) (guard : d387 pattern = 1) : d20 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c464 pattern childGuard
    simpa only [d387, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c511 pattern childGuard
    simpa only [d387, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1068 (pattern : Ten) (guard : d387 pattern = 1) : d143 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d143, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1066 pattern childGuard
    simpa only [d143, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d143, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1067 pattern childGuard
    simpa only [d143, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1069 (pattern : Ten) (guard : d387 pattern = 1) : d145 pattern ≤ (0 : Int) + d115 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d145, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1064 pattern childGuard
    simpa only [d145, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d145, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1068 pattern childGuard
    simpa only [d145, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1070 (pattern : Ten) (guard : d0 pattern = 1) : d16 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1071 (pattern : Ten) (guard : d387 pattern = 1) : d141 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1062 pattern childGuard
    simpa only [d387, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1070 pattern childGuard
    simpa only [d387, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1072 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1073 (pattern : Ten) (guard : d384 pattern = 1) : d16 pattern ≤ (0 : Int) + d44 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d16, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c412 pattern childGuard
    simpa only [d384, d16, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d16, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1072 pattern childGuard
    simpa only [d384, d16, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1074 (pattern : Ten) (guard : d387 pattern = 1) : d22 pattern ≤ (0 : Int) + d44 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1073 pattern childGuard
    simpa only [d387, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c519 pattern childGuard
    simpa only [d387, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1075 (pattern : Ten) (guard : d387 pattern = 1) : d144 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d144, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1071 pattern childGuard
    simpa only [d144, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d144, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1074 pattern childGuard
    simpa only [d144, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1076 (pattern : Ten) (guard : d387 pattern = 1) : d146 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d146, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1075 pattern childGuard
    simpa only [d146, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d146, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1068 pattern childGuard
    simpa only [d146, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1077 (pattern : Ten) (guard : d387 pattern = 1) : d147 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d147, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1069 pattern childGuard
    simpa only [d147, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d147, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1076 pattern childGuard
    simpa only [d147, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1078 (pattern : Ten) (guard : d387 pattern = 1) : d26 pattern ≤ (0 : Int) + d112 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d26, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1063 pattern childGuard
    simpa only [d26, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d26, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d26, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1079 (pattern : Ten) (guard : d387 pattern = 1) : d27 pattern ≤ (0 : Int) + d113 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d27, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1067 pattern childGuard
    simpa only [d27, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d27, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d27, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1080 (pattern : Ten) (guard : d387 pattern = 1) : d31 pattern ≤ (0 : Int) + d117 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d31, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1078 pattern childGuard
    simpa only [d31, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d31, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1079 pattern childGuard
    simpa only [d31, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1081 (pattern : Ten) (guard : d387 pattern = 1) : d28 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d28, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1074 pattern childGuard
    simpa only [d28, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d28, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d28, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1082 (pattern : Ten) (guard : d387 pattern = 1) : d32 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d32, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1081 pattern childGuard
    simpa only [d32, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d32, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1079 pattern childGuard
    simpa only [d32, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1083 (pattern : Ten) (guard : d387 pattern = 1) : d34 pattern ≤ (0 : Int) + d120 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1080 pattern childGuard
    simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1082 pattern childGuard
    simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1084 (pattern : Ten) (guard : d387 pattern = 1) : d148 pattern ≤ (0 : Int) + d121 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d148, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1077 pattern childGuard
    simpa only [d148, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d148, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1083 pattern childGuard
    simpa only [d148, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1085 (pattern : Ten) (guard : d387 pattern = 1) : d36 pattern ≤ (0 : Int) + d122 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1083 pattern childGuard
    simpa only [d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1086 (pattern : Ten) (guard : d387 pattern = 1) : d149 pattern ≤ (0 : Int) + d123 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d149, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1084 pattern childGuard
    simpa only [d149, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d149, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1085 pattern childGuard
    simpa only [d149, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1087 (pattern : Ten) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1088 (pattern : Ten) (guard : d388 pattern = 1) : d173 pattern ≤ (0 : Int) + d266 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c534 pattern childGuard
    simpa only [d388, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1087 pattern childGuard
    simpa only [d388, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1089 (pattern : Ten) (guard : d388 pattern = 1) : d177 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c534 pattern childGuard
    simpa only [d388, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c538 pattern childGuard
    simpa only [d388, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1090 (pattern : Ten) (guard : d388 pattern = 1) : d302 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d302, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1088 pattern childGuard
    simpa only [d302, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d302, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1089 pattern childGuard
    simpa only [d302, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1091 (pattern : Ten) (guard : d388 pattern = 1) : d181 pattern ≤ (0 : Int) + d268 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d181, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1089 pattern childGuard
    simpa only [d181, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d181, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d181, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1092 (pattern : Ten) (guard : d388 pattern = 1) : d304 pattern ≤ (0 : Int) + d271 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d304, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1090 pattern childGuard
    simpa only [d304, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d304, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1091 pattern childGuard
    simpa only [d304, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1093 (pattern : Ten) (guard : d0 pattern = 1) : d175 pattern ≤ (0 : Int) + d174 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1094 (pattern : Ten) (guard : d388 pattern = 1) : d301 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c534 pattern childGuard
    simpa only [d388, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1093 pattern childGuard
    simpa only [d388, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1095 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1096 (pattern : Ten) (guard : d383 pattern = 1) : d175 pattern ≤ (0 : Int) + d199 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d175, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d383, d175, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d175, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1095 pattern childGuard
    simpa only [d383, d175, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1097 (pattern : Ten) (guard : d388 pattern = 1) : d179 pattern ≤ (0 : Int) + d199 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1096 pattern childGuard
    simpa only [d388, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c548 pattern childGuard
    simpa only [d388, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1098 (pattern : Ten) (guard : d388 pattern = 1) : d303 pattern ≤ (0 : Int) + d269 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d303, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1094 pattern childGuard
    simpa only [d303, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d303, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1097 pattern childGuard
    simpa only [d303, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1099 (pattern : Ten) (guard : d388 pattern = 1) : d305 pattern ≤ (0 : Int) + d272 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d305, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1098 pattern childGuard
    simpa only [d305, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d305, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1091 pattern childGuard
    simpa only [d305, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1100 (pattern : Ten) (guard : d388 pattern = 1) : d306 pattern ≤ (0 : Int) + d275 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d306, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1092 pattern childGuard
    simpa only [d306, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d306, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1099 pattern childGuard
    simpa only [d306, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1101 (pattern : Ten) (guard : d388 pattern = 1) : d186 pattern ≤ (0 : Int) + d273 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d186, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1091 pattern childGuard
    simpa only [d186, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d186, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d186, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1102 (pattern : Ten) (guard : d388 pattern = 1) : d183 pattern ≤ (0 : Int) + d270 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d183, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1097 pattern childGuard
    simpa only [d183, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d183, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d183, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1103 (pattern : Ten) (guard : d388 pattern = 1) : d187 pattern ≤ (0 : Int) + d274 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d187, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1102 pattern childGuard
    simpa only [d187, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d187, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d187, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1104 (pattern : Ten) (guard : d388 pattern = 1) : d189 pattern ≤ (0 : Int) + d276 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d189, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1101 pattern childGuard
    simpa only [d189, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d189, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1103 pattern childGuard
    simpa only [d189, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1105 (pattern : Ten) (guard : d388 pattern = 1) : d307 pattern ≤ (0 : Int) + d277 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d307, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1100 pattern childGuard
    simpa only [d307, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d307, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1104 pattern childGuard
    simpa only [d307, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1106 (pattern : Ten) (guard : d388 pattern = 1) : d191 pattern ≤ (0 : Int) + d278 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d191, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1104 pattern childGuard
    simpa only [d191, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d191, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d191, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1107 (pattern : Ten) (guard : d388 pattern = 1) : d308 pattern ≤ (0 : Int) + d279 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d308, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1105 pattern childGuard
    simpa only [d308, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d308, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1106 pattern childGuard
    simpa only [d308, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1108 (pattern : Ten) (guard : d0 pattern = 1) : d137 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1109 (pattern : Ten) (guard : d384 pattern = 1) : d138 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1108 pattern childGuard
    simpa only [d384, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1110 (pattern : Ten) (guard : d384 pattern = 1) : d139 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d139, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1109 pattern childGuard
    simpa only [d139, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d139, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c458 pattern childGuard
    simpa only [d139, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1111 (pattern : Ten) (guard : d384 pattern = 1) : d142 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d142, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1110 pattern childGuard
    simpa only [d142, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d142, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c460 pattern childGuard
    simpa only [d142, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1112 (pattern : Ten) (guard : d384 pattern = 1) : d12 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c404 pattern childGuard
    simpa only [d384, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1113 (pattern : Ten) (guard : d384 pattern = 1) : d140 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d140, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1112 pattern childGuard
    simpa only [d140, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d140, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c464 pattern childGuard
    simpa only [d140, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1114 (pattern : Ten) (guard : d384 pattern = 1) : d143 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d143, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1113 pattern childGuard
    simpa only [d143, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d143, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c466 pattern childGuard
    simpa only [d143, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1115 (pattern : Ten) (guard : d384 pattern = 1) : d145 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d145, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1111 pattern childGuard
    simpa only [d145, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d145, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1114 pattern childGuard
    simpa only [d145, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1116 (pattern : Ten) (guard : d384 pattern = 1) : d141 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d141, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1062 pattern childGuard
    simpa only [d141, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d141, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c471 pattern childGuard
    simpa only [d141, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1117 (pattern : Ten) (guard : d384 pattern = 1) : d144 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d144, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1116 pattern childGuard
    simpa only [d144, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d144, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c473 pattern childGuard
    simpa only [d144, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1118 (pattern : Ten) (guard : d384 pattern = 1) : d146 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d146, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1117 pattern childGuard
    simpa only [d146, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d146, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1114 pattern childGuard
    simpa only [d146, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1119 (pattern : Ten) (guard : d384 pattern = 1) : d147 pattern ≤ (0 : Int) + d33 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d147, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1115 pattern childGuard
    simpa only [d147, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d147, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1118 pattern childGuard
    simpa only [d147, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
