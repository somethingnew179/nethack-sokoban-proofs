import NetHack.Soko22Hazard87.Compare192
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48250 (p : Pattern) (guard : d277237 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d277237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d277237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d277236 p = 1 := by simpa only [d277237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48249 p hg
    simpa only [d277237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48251 (p : Pattern) (guard : d277238 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d277238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d277238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d277237 p = 1 := by simpa only [d277238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48250 p hg
    simpa only [d277238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48252 (p : Pattern) (guard : d277239 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d277239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d277239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d277238 p = 1 := by simpa only [d277239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48251 p hg
    simpa only [d277239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48253 (p : Pattern) (guard : d44996 p = 1) : d47617 p ≤ (0 : Int) + d47617 p := by
  omega
theorem compare48254 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (0 : Int) + d49390 p := by
  have ha := bounds4 p
  have hb := bounds49390 p
  omega
theorem compare48255 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (0 : Int) + d47656 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48256 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (0 : Int) + d49391 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, d49391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48254 p hg
    simpa only [d15, d47617, d49391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, d49391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48255 p hg
    simpa only [d15, d47617, d49391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48257 (p : Pattern) (guard : d45587 p = 1) : d47617 p ≤ (0 : Int) + d49391 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48068 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48256 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48258 (p : Pattern) (guard : d45588 p = 1) : d47617 p ≤ (0 : Int) + d49392 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d45588, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48253 p hg
    simpa only [d45588, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d45588, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48257 p hg
    simpa only [d45588, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48259 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (0 : Int) + d49394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48260 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (0 : Int) + d49393 p := by
  have ha := bounds4 p
  have hb := bounds49393 p
  omega
theorem compare48261 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (0 : Int) + d47789 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48262 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (0 : Int) + d49394 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, d49394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48260 p hg
    simpa only [d15, d47617, d49394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, d49394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48261 p hg
    simpa only [d15, d47617, d49394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48263 (p : Pattern) (guard : d45587 p = 1) : d47617 p ≤ (0 : Int) + d49394 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48259 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48262 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48264 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (0 : Int) + d47938 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48265 (p : Pattern) (guard : d46472 p = 1) : d47617 p ≤ (0 : Int) + d49395 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48263 p hg
    simpa only [d46472, d49395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48264 p hg
    simpa only [d46472, d49395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48266 (p : Pattern) (guard : d369384 p = 1) : d47617 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 224 with
  | false =>
    have hg : d45588 p = 1 := by simpa only [d369384, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48258 p hg
    simpa only [d369384, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46472 p = 1 := by simpa only [d369384, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48265 p hg
    simpa only [d369384, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48267 (p : Pattern) (guard : d369385 p = 1) : d47617 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 223 with
  | false =>
    have hg : d369384 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48266 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48268 (p : Pattern) (guard : d369386 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369385 p = 1 := by simpa only [d369386, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48267 p hg
    simpa only [d369386, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369386, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48073 p hg
    simpa only [d369386, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48269 (p : Pattern) (guard : d369387 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369386 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48268 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48074 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48270 (p : Pattern) (guard : d369388 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48269 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275501 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48075 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48271 (p : Pattern) (guard : d369389 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369388 p = 1 := by simpa only [d369389, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48270 p hg
    simpa only [d369389, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369389, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48077 p hg
    simpa only [d369389, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48272 (p : Pattern) (guard : d369390 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48271 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48078 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48273 (p : Pattern) (guard : d369391 p = 1) : d50570 p ≤ (0 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369390 p = 1 := by simpa only [d369391, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48272 p hg
    simpa only [d369391, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369391, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48081 p hg
    simpa only [d369391, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48274 (p : Pattern) (guard : d369392 p = 1) : d50571 p ≤ (0 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369391 p = 1 := by simpa only [d369392, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48273 p hg
    simpa only [d369392, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369392, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48083 p hg
    simpa only [d369392, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48275 (p : Pattern) (guard : d369393 p = 1) : d50572 p ≤ (0 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369393, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48066 p hg
    simpa only [d369393, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369392 p = 1 := by simpa only [d369393, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48274 p hg
    simpa only [d369393, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48276 (p : Pattern) (guard : d369394 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369393 p = 1 := by simpa only [d369394, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48275 p hg
    simpa only [d369394, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369394, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48086 p hg
    simpa only [d369394, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48277 (p : Pattern) (guard : d369395 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369394 p = 1 := by simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48276 p hg
    simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275508 p = 1 := by simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48087 p hg
    simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48278 (p : Pattern) (guard : d369396 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369395 p = 1 := by simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48277 p hg
    simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275509 p = 1 := by simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48089 p hg
    simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48279 (p : Pattern) (guard : d369397 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369396 p = 1 := by simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48278 p hg
    simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275510 p = 1 := by simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48090 p hg
    simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48280 (p : Pattern) (guard : d369398 p = 1) : d50577 p ≤ (0 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369398, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48065 p hg
    simpa only [d369398, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369397 p = 1 := by simpa only [d369398, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48279 p hg
    simpa only [d369398, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48281 (p : Pattern) (guard : d369399 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369399, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48064 p hg
    simpa only [d369399, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369398 p = 1 := by simpa only [d369399, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48280 p hg
    simpa only [d369399, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48282 (p : Pattern) (guard : d369400 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369399 p = 1 := by simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48281 p hg
    simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275513 p = 1 := by simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48093 p hg
    simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48283 (p : Pattern) (guard : d369401 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369400 p = 1 := by simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48282 p hg
    simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275514 p = 1 := by simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48095 p hg
    simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48284 (p : Pattern) (guard : d369402 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369401 p = 1 := by simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48283 p hg
    simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48285 (p : Pattern) (guard : d369403 p = 1) : d50590 p ≤ (0 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369402 p = 1 := by simpa only [d369403, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48284 p hg
    simpa only [d369403, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369403, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48098 p hg
    simpa only [d369403, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48286 (p : Pattern) (guard : d369404 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369404, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d369404, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369403 p = 1 := by simpa only [d369404, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48285 p hg
    simpa only [d369404, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48287 (p : Pattern) (guard : d369405 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369404 p = 1 := by simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48286 p hg
    simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275518 p = 1 := by simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48100 p hg
    simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48288 (p : Pattern) (guard : d369406 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369405 p = 1 := by simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48287 p hg
    simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48289 (p : Pattern) (guard : d369407 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369406 p = 1 := by simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48288 p hg
    simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48290 (p : Pattern) (guard : d369408 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369407 p = 1 := by simpa only [d369408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48289 p hg
    simpa only [d369408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48291 (p : Pattern) (guard : d369409 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369408 p = 1 := by simpa only [d369409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48290 p hg
    simpa only [d369409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275522 p = 1 := by simpa only [d369409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48104 p hg
    simpa only [d369409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48292 (p : Pattern) (guard : d369470 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369409 p = 1 := by simpa only [d369470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48291 p hg
    simpa only [d369470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48293 (p : Pattern) (guard : d369471 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369470 p = 1 := by simpa only [d369471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48292 p hg
    simpa only [d369471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48294 (p : Pattern) (guard : d369472 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369471 p = 1 := by simpa only [d369472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48293 p hg
    simpa only [d369472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48295 (p : Pattern) (guard : d369473 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369472 p = 1 := by simpa only [d369473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48294 p hg
    simpa only [d369473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48296 (p : Pattern) (guard : d369474 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369473 p = 1 := by simpa only [d369474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48295 p hg
    simpa only [d369474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48297 (p : Pattern) (guard : d369415 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369407 p = 1 := by simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48289 p hg
    simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48298 (p : Pattern) (guard : d369416 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369415 p = 1 := by simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48297 p hg
    simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275529 p = 1 := by simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48111 p hg
    simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48299 (p : Pattern) (guard : d369477 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369416 p = 1 := by simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48298 p hg
    simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48300 (p : Pattern) (guard : d369478 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369477 p = 1 := by simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48299 p hg
    simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48301 (p : Pattern) (guard : d369479 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369478 p = 1 := by simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48300 p hg
    simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48302 (p : Pattern) (guard : d369480 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369479 p = 1 := by simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48301 p hg
    simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48303 (p : Pattern) (guard : d369481 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369473 p = 1 := by simpa only [d369481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48295 p hg
    simpa only [d369481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369480 p = 1 := by simpa only [d369481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48302 p hg
    simpa only [d369481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48304 (p : Pattern) (guard : d369482 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369474 p = 1 := by simpa only [d369482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48296 p hg
    simpa only [d369482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369481 p = 1 := by simpa only [d369482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48303 p hg
    simpa only [d369482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48305 (p : Pattern) (guard : d369483 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369482 p = 1 := by simpa only [d369483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48304 p hg
    simpa only [d369483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48306 (p : Pattern) (guard : d370469 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369483 p = 1 := by simpa only [d370469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48305 p hg
    simpa only [d370469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48307 (p : Pattern) (guard : d370470 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370469 p = 1 := by simpa only [d370470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48306 p hg
    simpa only [d370470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48308 (p : Pattern) (guard : d44996 p = 1) : d47706 p ≤ (0 : Int) + d47706 p := by
  omega
theorem compare48309 (p : Pattern) (guard : d14 p = 1) : d5 p ≤ (0 : Int) + d49559 p := by
  have ha := bounds5 p
  have hb := bounds49559 p
  omega
theorem compare48310 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (0 : Int) + d47638 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48311 (p : Pattern) (guard : d15 p = 1) : d47706 p ≤ (0 : Int) + d49560 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47706, d49560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48309 p hg
    simpa only [d15, d47706, d49560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47706, d49560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48310 p hg
    simpa only [d15, d47706, d49560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48312 (p : Pattern) (guard : d45587 p = 1) : d47706 p ≤ (0 : Int) + d49560 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48129 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48311 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48313 (p : Pattern) (guard : d45588 p = 1) : d47706 p ≤ (0 : Int) + d49561 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d45588, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48308 p hg
    simpa only [d45588, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d45588, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48312 p hg
    simpa only [d45588, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48314 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (0 : Int) + d49563 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48315 (p : Pattern) (guard : d14 p = 1) : d5 p ≤ (0 : Int) + d49562 p := by
  have ha := bounds5 p
  have hb := bounds49562 p
  omega
theorem compare48316 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (0 : Int) + d47622 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48317 (p : Pattern) (guard : d15 p = 1) : d47706 p ≤ (0 : Int) + d49563 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47706, d49563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48315 p hg
    simpa only [d15, d47706, d49563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47706, d49563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48316 p hg
    simpa only [d15, d47706, d49563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48318 (p : Pattern) (guard : d45587 p = 1) : d47706 p ≤ (0 : Int) + d49563 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48314 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48317 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48319 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (0 : Int) + d47947 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48320 (p : Pattern) (guard : d46472 p = 1) : d47706 p ≤ (0 : Int) + d49564 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48318 p hg
    simpa only [d46472, d49564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48319 p hg
    simpa only [d46472, d49564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48321 (p : Pattern) (guard : d369384 p = 1) : d47706 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 224 with
  | false =>
    have hg : d45588 p = 1 := by simpa only [d369384, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48313 p hg
    simpa only [d369384, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46472 p = 1 := by simpa only [d369384, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48320 p hg
    simpa only [d369384, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48322 (p : Pattern) (guard : d369385 p = 1) : d47706 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 223 with
  | false =>
    have hg : d369384 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48321 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48323 (p : Pattern) (guard : d369386 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369385 p = 1 := by simpa only [d369386, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48322 p hg
    simpa only [d369386, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369386, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48134 p hg
    simpa only [d369386, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48324 (p : Pattern) (guard : d369387 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369386 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48323 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48135 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48325 (p : Pattern) (guard : d369388 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48324 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275501 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48136 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48326 (p : Pattern) (guard : d369389 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369388 p = 1 := by simpa only [d369389, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48325 p hg
    simpa only [d369389, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369389, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48138 p hg
    simpa only [d369389, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48327 (p : Pattern) (guard : d369390 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48326 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48139 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48328 (p : Pattern) (guard : d369391 p = 1) : d50657 p ≤ (0 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369390 p = 1 := by simpa only [d369391, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48327 p hg
    simpa only [d369391, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369391, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369391, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48329 (p : Pattern) (guard : d369392 p = 1) : d50658 p ≤ (0 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369391 p = 1 := by simpa only [d369392, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48328 p hg
    simpa only [d369392, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369392, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369392, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48330 (p : Pattern) (guard : d369393 p = 1) : d50659 p ≤ (0 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369393, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48127 p hg
    simpa only [d369393, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369392 p = 1 := by simpa only [d369393, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48329 p hg
    simpa only [d369393, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48331 (p : Pattern) (guard : d369394 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369393 p = 1 := by simpa only [d369394, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48330 p hg
    simpa only [d369394, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369394, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48146 p hg
    simpa only [d369394, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48332 (p : Pattern) (guard : d369395 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369394 p = 1 := by simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48331 p hg
    simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275508 p = 1 := by simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48147 p hg
    simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48333 (p : Pattern) (guard : d369396 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369395 p = 1 := by simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48332 p hg
    simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275509 p = 1 := by simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48149 p hg
    simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48334 (p : Pattern) (guard : d369397 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369396 p = 1 := by simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48333 p hg
    simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275510 p = 1 := by simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48150 p hg
    simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48335 (p : Pattern) (guard : d369398 p = 1) : d50664 p ≤ (0 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369398, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48126 p hg
    simpa only [d369398, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369397 p = 1 := by simpa only [d369398, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48334 p hg
    simpa only [d369398, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48336 (p : Pattern) (guard : d369399 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369399, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48125 p hg
    simpa only [d369399, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369398 p = 1 := by simpa only [d369399, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48335 p hg
    simpa only [d369399, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48337 (p : Pattern) (guard : d369400 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369399 p = 1 := by simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48336 p hg
    simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275513 p = 1 := by simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48153 p hg
    simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48338 (p : Pattern) (guard : d369401 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369400 p = 1 := by simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48337 p hg
    simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275514 p = 1 := by simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48155 p hg
    simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48339 (p : Pattern) (guard : d369402 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369401 p = 1 := by simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48338 p hg
    simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48340 (p : Pattern) (guard : d369403 p = 1) : d50673 p ≤ (0 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369402 p = 1 := by simpa only [d369403, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48339 p hg
    simpa only [d369403, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369403, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48158 p hg
    simpa only [d369403, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48341 (p : Pattern) (guard : d369404 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369404, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48124 p hg
    simpa only [d369404, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369403 p = 1 := by simpa only [d369404, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48340 p hg
    simpa only [d369404, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48342 (p : Pattern) (guard : d369405 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369404 p = 1 := by simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48341 p hg
    simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275518 p = 1 := by simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48160 p hg
    simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48343 (p : Pattern) (guard : d369406 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369405 p = 1 := by simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48342 p hg
    simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48344 (p : Pattern) (guard : d369407 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369406 p = 1 := by simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48343 p hg
    simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48345 (p : Pattern) (guard : d369415 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369407 p = 1 := by simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48344 p hg
    simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48346 (p : Pattern) (guard : d369416 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369415 p = 1 := by simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48345 p hg
    simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275529 p = 1 := by simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48164 p hg
    simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48347 (p : Pattern) (guard : d369477 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369416 p = 1 := by simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48346 p hg
    simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48348 (p : Pattern) (guard : d369478 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369477 p = 1 := by simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48347 p hg
    simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48349 (p : Pattern) (guard : d369479 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369478 p = 1 := by simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48348 p hg
    simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48350 (p : Pattern) (guard : d369480 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369479 p = 1 := by simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48349 p hg
    simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48351 (p : Pattern) (guard : d370471 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370471, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370471, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369480 p = 1 := by simpa only [d370471, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48350 p hg
    simpa only [d370471, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48352 (p : Pattern) (guard : d370472 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370471 p = 1 := by simpa only [d370472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48351 p hg
    simpa only [d370472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48353 (p : Pattern) (guard : d370473 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 69 with
  | false =>
    have hg : d370472 p = 1 := by simpa only [d370473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48352 p hg
    simpa only [d370473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48354 (p : Pattern) (guard : d370474 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 51 with
  | false =>
    have hg : d370473 p = 1 := by simpa only [d370474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48353 p hg
    simpa only [d370474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48355 (p : Pattern) (guard : d370475 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 50 with
  | false =>
    have hg : d370474 p = 1 := by simpa only [d370475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48354 p hg
    simpa only [d370475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48356 (p : Pattern) (guard : d370476 p = 1) : d50676 p ≤ (0 : Int) + d367880 p := by
  cases selected : p 49 with
  | false =>
    have hg : d370470 p = 1 := by simpa only [d370476, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48307 p hg
    simpa only [d370476, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370475 p = 1 := by simpa only [d370476, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48355 p hg
    simpa only [d370476, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48357 (p : Pattern) (guard : d44996 p = 1) : d47630 p ≤ (0 : Int) + d47630 p := by
  omega
theorem compare48358 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (0 : Int) + d49309 p := by
  have ha := bounds2 p
  have hb := bounds49309 p
  omega
theorem compare48359 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (0 : Int) + d47789 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48360 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (0 : Int) + d49310 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d49310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48358 p hg
    simpa only [d15, d47630, d49310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d49310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48359 p hg
    simpa only [d15, d47630, d49310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48361 (p : Pattern) (guard : d45587 p = 1) : d47630 p ≤ (0 : Int) + d49310 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48182 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48360 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48362 (p : Pattern) (guard : d45588 p = 1) : d47630 p ≤ (0 : Int) + d49311 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d45588, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48357 p hg
    simpa only [d45588, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d45588, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48361 p hg
    simpa only [d45588, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48363 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (0 : Int) + d49313 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48364 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (0 : Int) + d49312 p := by
  have ha := bounds2 p
  have hb := bounds49312 p
  omega
theorem compare48365 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (0 : Int) + d47633 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48366 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (0 : Int) + d49313 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d49313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48364 p hg
    simpa only [d15, d47630, d49313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d49313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48365 p hg
    simpa only [d15, d47630, d49313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48367 (p : Pattern) (guard : d45587 p = 1) : d47630 p ≤ (0 : Int) + d49313 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48363 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48366 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48368 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (0 : Int) + d49314 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48369 (p : Pattern) (guard : d46472 p = 1) : d47630 p ≤ (0 : Int) + d49315 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48367 p hg
    simpa only [d46472, d49315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48368 p hg
    simpa only [d46472, d49315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48370 (p : Pattern) (guard : d369384 p = 1) : d47630 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 224 with
  | false =>
    have hg : d45588 p = 1 := by simpa only [d369384, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48362 p hg
    simpa only [d369384, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46472 p = 1 := by simpa only [d369384, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48369 p hg
    simpa only [d369384, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48371 (p : Pattern) (guard : d369385 p = 1) : d47630 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 223 with
  | false =>
    have hg : d369384 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48370 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48372 (p : Pattern) (guard : d369386 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369385 p = 1 := by simpa only [d369386, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48371 p hg
    simpa only [d369386, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369386, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48187 p hg
    simpa only [d369386, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48373 (p : Pattern) (guard : d369387 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369386 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48372 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48188 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48374 (p : Pattern) (guard : d369388 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48373 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275501 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48189 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48375 (p : Pattern) (guard : d369389 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369388 p = 1 := by simpa only [d369389, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48374 p hg
    simpa only [d369389, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369389, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48191 p hg
    simpa only [d369389, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48376 (p : Pattern) (guard : d369390 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48375 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48192 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48377 (p : Pattern) (guard : d369434 p = 1) : d50726 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369434, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d369434, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369390 p = 1 := by simpa only [d369434, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48376 p hg
    simpa only [d369434, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48378 (p : Pattern) (guard : d369391 p = 1) : d50727 p ≤ (0 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369390 p = 1 := by simpa only [d369391, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48272 p hg
    simpa only [d369391, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369391, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369391, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48379 (p : Pattern) (guard : d369435 p = 1) : d50728 p ≤ (0 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369434 p = 1 := by simpa only [d369435, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48377 p hg
    simpa only [d369435, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369391 p = 1 := by simpa only [d369435, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48378 p hg
    simpa only [d369435, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48380 (p : Pattern) (guard : d44996 p = 1) : d47634 p ≤ (0 : Int) + d47634 p := by
  omega
theorem compare48381 (p : Pattern) (guard : d14 p = 1) : d6 p ≤ (0 : Int) + d47633 p := by
  have ha := bounds6 p
  have hb := bounds47633 p
  omega
theorem compare48382 (p : Pattern) (guard : d0 p = 1) : d47633 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48383 (p : Pattern) (guard : d15 p = 1) : d47634 p ≤ (0 : Int) + d47963 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47634, d47963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48381 p hg
    simpa only [d15, d47634, d47963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47634, d47963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48382 p hg
    simpa only [d15, d47634, d47963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48384 (p : Pattern) (guard : d45587 p = 1) : d47634 p ≤ (0 : Int) + d47963 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48199 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48383 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48385 (p : Pattern) (guard : d45588 p = 1) : d47634 p ≤ (0 : Int) + d49319 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d45588, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48380 p hg
    simpa only [d45588, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d45588, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48384 p hg
    simpa only [d45588, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48386 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (0 : Int) + d49321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48387 (p : Pattern) (guard : d14 p = 1) : d6 p ≤ (0 : Int) + d49320 p := by
  have ha := bounds6 p
  have hb := bounds49320 p
  omega
theorem compare48388 (p : Pattern) (guard : d0 p = 1) : d47633 p ≤ (0 : Int) + d47656 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48389 (p : Pattern) (guard : d15 p = 1) : d47634 p ≤ (0 : Int) + d49321 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47634, d49321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48387 p hg
    simpa only [d15, d47634, d49321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47634, d49321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48388 p hg
    simpa only [d15, d47634, d49321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48390 (p : Pattern) (guard : d45587 p = 1) : d47634 p ≤ (0 : Int) + d49321 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48386 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48389 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48391 (p : Pattern) (guard : d46472 p = 1) : d47634 p ≤ (0 : Int) + d49322 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48390 p hg
    simpa only [d46472, d49322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48199 p hg
    simpa only [d46472, d49322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48392 (p : Pattern) (guard : d369384 p = 1) : d47634 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d45588 p = 1 := by simpa only [d369384, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48385 p hg
    simpa only [d369384, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46472 p = 1 := by simpa only [d369384, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48391 p hg
    simpa only [d369384, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48393 (p : Pattern) (guard : d369385 p = 1) : d47634 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 223 with
  | false =>
    have hg : d369384 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48392 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48394 (p : Pattern) (guard : d369386 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369385 p = 1 := by simpa only [d369386, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48393 p hg
    simpa only [d369386, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369386, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48204 p hg
    simpa only [d369386, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48395 (p : Pattern) (guard : d369387 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369386 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48394 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48205 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48396 (p : Pattern) (guard : d369388 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48395 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275501 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48206 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48397 (p : Pattern) (guard : d369389 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369388 p = 1 := by simpa only [d369389, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48396 p hg
    simpa only [d369389, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369389, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48208 p hg
    simpa only [d369389, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48398 (p : Pattern) (guard : d369390 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48397 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48209 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48399 (p : Pattern) (guard : d369391 p = 1) : d50573 p ≤ (0 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369390 p = 1 := by simpa only [d369391, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48398 p hg
    simpa only [d369391, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369391, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369391, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48400 (p : Pattern) (guard : d369392 p = 1) : d50574 p ≤ (0 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369391 p = 1 := by simpa only [d369392, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48399 p hg
    simpa only [d369392, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369392, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369392, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48401 (p : Pattern) (guard : d369436 p = 1) : d50729 p ≤ (0 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369435 p = 1 := by simpa only [d369436, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48379 p hg
    simpa only [d369436, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369392 p = 1 := by simpa only [d369436, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48400 p hg
    simpa only [d369436, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48402 (p : Pattern) (guard : d369437 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369436 p = 1 := by simpa only [d369437, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48401 p hg
    simpa only [d369437, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369437, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48215 p hg
    simpa only [d369437, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48403 (p : Pattern) (guard : d369438 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369437 p = 1 := by simpa only [d369438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48402 p hg
    simpa only [d369438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275549 p = 1 := by simpa only [d369438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48216 p hg
    simpa only [d369438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48404 (p : Pattern) (guard : d369439 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369438 p = 1 := by simpa only [d369439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48403 p hg
    simpa only [d369439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275550 p = 1 := by simpa only [d369439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48218 p hg
    simpa only [d369439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48405 (p : Pattern) (guard : d369440 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369439 p = 1 := by simpa only [d369440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48404 p hg
    simpa only [d369440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275551 p = 1 := by simpa only [d369440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48219 p hg
    simpa only [d369440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48406 (p : Pattern) (guard : d369441 p = 1) : d50734 p ≤ (0 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369441, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48179 p hg
    simpa only [d369441, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369440 p = 1 := by simpa only [d369441, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48405 p hg
    simpa only [d369441, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48407 (p : Pattern) (guard : d369442 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369442, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48178 p hg
    simpa only [d369442, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369441 p = 1 := by simpa only [d369442, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48406 p hg
    simpa only [d369442, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48408 (p : Pattern) (guard : d369443 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369442 p = 1 := by simpa only [d369443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48407 p hg
    simpa only [d369443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275554 p = 1 := by simpa only [d369443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48222 p hg
    simpa only [d369443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48409 (p : Pattern) (guard : d369444 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369443 p = 1 := by simpa only [d369444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48408 p hg
    simpa only [d369444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275555 p = 1 := by simpa only [d369444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48224 p hg
    simpa only [d369444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48410 (p : Pattern) (guard : d369445 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369444 p = 1 := by simpa only [d369445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48409 p hg
    simpa only [d369445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d369445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48411 (p : Pattern) (guard : d369446 p = 1) : d50737 p ≤ (0 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369445 p = 1 := by simpa only [d369446, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48410 p hg
    simpa only [d369446, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369446, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48227 p hg
    simpa only [d369446, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48412 (p : Pattern) (guard : d369447 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369447, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d369447, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369446 p = 1 := by simpa only [d369447, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48411 p hg
    simpa only [d369447, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48413 (p : Pattern) (guard : d369448 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369447 p = 1 := by simpa only [d369448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48412 p hg
    simpa only [d369448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275559 p = 1 := by simpa only [d369448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48229 p hg
    simpa only [d369448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48414 (p : Pattern) (guard : d369449 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369448 p = 1 := by simpa only [d369449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48413 p hg
    simpa only [d369449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48415 (p : Pattern) (guard : d369450 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369449 p = 1 := by simpa only [d369450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48414 p hg
    simpa only [d369450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48416 (p : Pattern) (guard : d369451 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369450 p = 1 := by simpa only [d369451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48415 p hg
    simpa only [d369451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48417 (p : Pattern) (guard : d369452 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369451 p = 1 := by simpa only [d369452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48416 p hg
    simpa only [d369452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275563 p = 1 := by simpa only [d369452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48233 p hg
    simpa only [d369452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48418 (p : Pattern) (guard : d370477 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369452 p = 1 := by simpa only [d370477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48417 p hg
    simpa only [d370477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48419 (p : Pattern) (guard : d370478 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d370477 p = 1 := by simpa only [d370478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48418 p hg
    simpa only [d370478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48420 (p : Pattern) (guard : d370479 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370478 p = 1 := by simpa only [d370479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48419 p hg
    simpa only [d370479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48421 (p : Pattern) (guard : d370480 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370479 p = 1 := by simpa only [d370480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48420 p hg
    simpa only [d370480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48422 (p : Pattern) (guard : d370481 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370481, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370481, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370480 p = 1 := by simpa only [d370481, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48421 p hg
    simpa only [d370481, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48423 (p : Pattern) (guard : d370482 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370481 p = 1 := by simpa only [d370482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48422 p hg
    simpa only [d370482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48424 (p : Pattern) (guard : d370483 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 69 with
  | false =>
    have hg : d370482 p = 1 := by simpa only [d370483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48423 p hg
    simpa only [d370483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48425 (p : Pattern) (guard : d370484 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 51 with
  | false =>
    have hg : d370483 p = 1 := by simpa only [d370484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48424 p hg
    simpa only [d370484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48426 (p : Pattern) (guard : d370485 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 50 with
  | false =>
    have hg : d370484 p = 1 := by simpa only [d370485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48425 p hg
    simpa only [d370485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48427 (p : Pattern) (guard : d370486 p = 1) : d50822 p ≤ (0 : Int) + d367984 p := by
  cases selected : p 49 with
  | false =>
    have hg : d370485 p = 1 := by simpa only [d370486, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48426 p hg
    simpa only [d370486, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370486, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48244 p hg
    simpa only [d370486, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48428 (p : Pattern) (guard : d370487 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 48 with
  | false =>
    have hg : d370476 p = 1 := by simpa only [d370487, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48356 p hg
    simpa only [d370487, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370486 p = 1 := by simpa only [d370487, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48427 p hg
    simpa only [d370487, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48429 (p : Pattern) (guard : d370488 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370487 p = 1 := by simpa only [d370488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48428 p hg
    simpa only [d370488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48430 (p : Pattern) (guard : d370489 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370488 p = 1 := by simpa only [d370489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48429 p hg
    simpa only [d370489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48431 (p : Pattern) (guard : d370490 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370489 p = 1 := by simpa only [d370490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48430 p hg
    simpa only [d370490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48432 (p : Pattern) (guard : d370491 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370490 p = 1 := by simpa only [d370491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48431 p hg
    simpa only [d370491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48433 (p : Pattern) (guard : d370492 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370491 p = 1 := by simpa only [d370492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48432 p hg
    simpa only [d370492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48434 (p : Pattern) (guard : d370493 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370492 p = 1 := by simpa only [d370493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48433 p hg
    simpa only [d370493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48435 (p : Pattern) (guard : d370494 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d277239 p = 1 := by simpa only [d370494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48252 p hg
    simpa only [d370494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370493 p = 1 := by simpa only [d370494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48434 p hg
    simpa only [d370494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48436 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (0 : Int) + d49392 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48437 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (0 : Int) + d47616 p := by
  have ha := bounds4 p
  have hb := bounds47616 p
  omega
theorem compare48438 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48439 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (0 : Int) + d47938 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, d47938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48437 p hg
    simpa only [d15, d47617, d47938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, d47938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48438 p hg
    simpa only [d15, d47617, d47938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48440 (p : Pattern) (guard : d45587 p = 1) : d47617 p ≤ (0 : Int) + d47938 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48264 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48439 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48441 (p : Pattern) (guard : d46040 p = 1) : d47617 p ≤ (0 : Int) + d49395 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46040, d49395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48259 p hg
    simpa only [d46040, d49395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d46040, d49395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48440 p hg
    simpa only [d46040, d49395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48442 (p : Pattern) (guard : d46041 p = 1) : d47617 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46041, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48436 p hg
    simpa only [d46041, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46040 p = 1 := by simpa only [d46041, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48441 p hg
    simpa only [d46041, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48443 (p : Pattern) (guard : d46042 p = 1) : d47617 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46041 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48442 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48444 (p : Pattern) (guard : d46043 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46042 p = 1 := by simpa only [d46043, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48443 p hg
    simpa only [d46043, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46043, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48073 p hg
    simpa only [d46043, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48445 (p : Pattern) (guard : d369497 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46043 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48444 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369386 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48268 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48446 (p : Pattern) (guard : d46459 p = 1) : d47617 p ≤ (0 : Int) + d49392 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d46459, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48253 p hg
    simpa only [d46459, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46459, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48068 p hg
    simpa only [d46459, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48447 (p : Pattern) (guard : d46460 p = 1) : d47617 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46459 p = 1 := by simpa only [d46460, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48446 p hg
    simpa only [d46460, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46460, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48070 p hg
    simpa only [d46460, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48448 (p : Pattern) (guard : d369498 p = 1) : d47617 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46460 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48447 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48449 (p : Pattern) (guard : d369499 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369498 p = 1 := by simpa only [d369499, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48448 p hg
    simpa only [d369499, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369499, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48073 p hg
    simpa only [d369499, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48450 (p : Pattern) (guard : d369500 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369499 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48449 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48074 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48451 (p : Pattern) (guard : d369501 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48445 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369500 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48450 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48452 (p : Pattern) (guard : d369502 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369501 p = 1 := by simpa only [d369502, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48451 p hg
    simpa only [d369502, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369502, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48077 p hg
    simpa only [d369502, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48453 (p : Pattern) (guard : d369503 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48452 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369389 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48271 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48454 (p : Pattern) (guard : d369504 p = 1) : d50570 p ≤ (0 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369503 p = 1 := by simpa only [d369504, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48453 p hg
    simpa only [d369504, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369504, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48081 p hg
    simpa only [d369504, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48455 (p : Pattern) (guard : d369505 p = 1) : d50571 p ≤ (0 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369504 p = 1 := by simpa only [d369505, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48454 p hg
    simpa only [d369505, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369505, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48083 p hg
    simpa only [d369505, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48456 (p : Pattern) (guard : d369506 p = 1) : d50572 p ≤ (0 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369506, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48066 p hg
    simpa only [d369506, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369505 p = 1 := by simpa only [d369506, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48455 p hg
    simpa only [d369506, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48457 (p : Pattern) (guard : d369507 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369506 p = 1 := by simpa only [d369507, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48456 p hg
    simpa only [d369507, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369507, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48086 p hg
    simpa only [d369507, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48458 (p : Pattern) (guard : d369508 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369507 p = 1 := by simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48457 p hg
    simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369394 p = 1 := by simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48276 p hg
    simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48459 (p : Pattern) (guard : d369509 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48269 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48460 (p : Pattern) (guard : d369510 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369509 p = 1 := by simpa only [d369510, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48459 p hg
    simpa only [d369510, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369510, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48077 p hg
    simpa only [d369510, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48461 (p : Pattern) (guard : d369511 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369510 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48460 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48078 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48462 (p : Pattern) (guard : d369512 p = 1) : d50570 p ≤ (0 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369511 p = 1 := by simpa only [d369512, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48461 p hg
    simpa only [d369512, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369512, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48081 p hg
    simpa only [d369512, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48463 (p : Pattern) (guard : d369513 p = 1) : d50571 p ≤ (0 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369512 p = 1 := by simpa only [d369513, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48462 p hg
    simpa only [d369513, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369513, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48083 p hg
    simpa only [d369513, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48464 (p : Pattern) (guard : d369514 p = 1) : d50572 p ≤ (0 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369514, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48066 p hg
    simpa only [d369514, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369513 p = 1 := by simpa only [d369514, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48463 p hg
    simpa only [d369514, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48465 (p : Pattern) (guard : d369515 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369514 p = 1 := by simpa only [d369515, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48464 p hg
    simpa only [d369515, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369515, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48086 p hg
    simpa only [d369515, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48466 (p : Pattern) (guard : d369516 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369515 p = 1 := by simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48465 p hg
    simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275508 p = 1 := by simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48087 p hg
    simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48467 (p : Pattern) (guard : d369517 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369508 p = 1 := by simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48458 p hg
    simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369516 p = 1 := by simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48466 p hg
    simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48468 (p : Pattern) (guard : d369518 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369517 p = 1 := by simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48467 p hg
    simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369396 p = 1 := by simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48278 p hg
    simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48469 (p : Pattern) (guard : d369519 p = 1) : d50577 p ≤ (0 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369519, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48065 p hg
    simpa only [d369519, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369518 p = 1 := by simpa only [d369519, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48468 p hg
    simpa only [d369519, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48470 (p : Pattern) (guard : d369520 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369520, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48064 p hg
    simpa only [d369520, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369519 p = 1 := by simpa only [d369520, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48469 p hg
    simpa only [d369520, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48471 (p : Pattern) (guard : d369521 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369520 p = 1 := by simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48470 p hg
    simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369399 p = 1 := by simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48281 p hg
    simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48472 (p : Pattern) (guard : d369623 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369399 p = 1 := by simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48281 p hg
    simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48473 (p : Pattern) (guard : d369624 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369521 p = 1 := by simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48471 p hg
    simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369623 p = 1 := by simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48472 p hg
    simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48474 (p : Pattern) (guard : d369625 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369624 p = 1 := by simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48473 p hg
    simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48475 (p : Pattern) (guard : d369626 p = 1) : d50590 p ≤ (0 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369625 p = 1 := by simpa only [d369626, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48474 p hg
    simpa only [d369626, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369626, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48098 p hg
    simpa only [d369626, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48476 (p : Pattern) (guard : d369627 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369627, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d369627, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369626 p = 1 := by simpa only [d369627, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48475 p hg
    simpa only [d369627, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48477 (p : Pattern) (guard : d369628 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369623 p = 1 := by simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48472 p hg
    simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48478 (p : Pattern) (guard : d369629 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369628 p = 1 := by simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48477 p hg
    simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48479 (p : Pattern) (guard : d369630 p = 1) : d50590 p ≤ (0 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369629 p = 1 := by simpa only [d369630, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48478 p hg
    simpa only [d369630, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369630, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48098 p hg
    simpa only [d369630, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48480 (p : Pattern) (guard : d369631 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369631, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d369631, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369630 p = 1 := by simpa only [d369631, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48479 p hg
    simpa only [d369631, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48481 (p : Pattern) (guard : d369632 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369627 p = 1 := by simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48476 p hg
    simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369631 p = 1 := by simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48480 p hg
    simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48482 (p : Pattern) (guard : d369633 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369632 p = 1 := by simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48481 p hg
    simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48483 (p : Pattern) (guard : d369634 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369633 p = 1 := by simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48482 p hg
    simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48484 (p : Pattern) (guard : d369635 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369634 p = 1 := by simpa only [d369635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48483 p hg
    simpa only [d369635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48485 (p : Pattern) (guard : d369636 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369631 p = 1 := by simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48480 p hg
    simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48486 (p : Pattern) (guard : d369637 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369636 p = 1 := by simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48485 p hg
    simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48487 (p : Pattern) (guard : d369638 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369637 p = 1 := by simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48486 p hg
    simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48488 (p : Pattern) (guard : d369639 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369638 p = 1 := by simpa only [d369639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48487 p hg
    simpa only [d369639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48489 (p : Pattern) (guard : d369640 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369635 p = 1 := by simpa only [d369640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48484 p hg
    simpa only [d369640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369639 p = 1 := by simpa only [d369640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48488 p hg
    simpa only [d369640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48490 (p : Pattern) (guard : d369641 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369640 p = 1 := by simpa only [d369641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48489 p hg
    simpa only [d369641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48491 (p : Pattern) (guard : d369642 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369641 p = 1 := by simpa only [d369642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48490 p hg
    simpa only [d369642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48492 (p : Pattern) (guard : d369643 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369642 p = 1 := by simpa only [d369643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48491 p hg
    simpa only [d369643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48493 (p : Pattern) (guard : d369644 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369643 p = 1 := by simpa only [d369644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48492 p hg
    simpa only [d369644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48494 (p : Pattern) (guard : d369645 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369644 p = 1 := by simpa only [d369645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48493 p hg
    simpa only [d369645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48495 (p : Pattern) (guard : d369648 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369634 p = 1 := by simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48483 p hg
    simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48496 (p : Pattern) (guard : d369649 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369638 p = 1 := by simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48487 p hg
    simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48497 (p : Pattern) (guard : d369650 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369648 p = 1 := by simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48495 p hg
    simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369649 p = 1 := by simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48496 p hg
    simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48498 (p : Pattern) (guard : d369651 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369650 p = 1 := by simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48497 p hg
    simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48499 (p : Pattern) (guard : d369652 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369651 p = 1 := by simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48498 p hg
    simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
