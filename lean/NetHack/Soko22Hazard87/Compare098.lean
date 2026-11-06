import NetHack.Soko22Hazard87.Compare097
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24500 (p : Pattern) (guard : d181235 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181224 p = 1 := by simpa only [d181235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24485 p hg
    simpa only [d181235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181234 p = 1 := by simpa only [d181235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24499 p hg
    simpa only [d181235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24501 (p : Pattern) (guard : d181236 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181236, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181236, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181235 p = 1 := by simpa only [d181236, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24500 p hg
    simpa only [d181236, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24502 (p : Pattern) (guard : d181237 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181237, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181237, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181236 p = 1 := by simpa only [d181237, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24501 p hg
    simpa only [d181237, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24503 (p : Pattern) (guard : d181238 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181227 p = 1 := by simpa only [d181238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24488 p hg
    simpa only [d181238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181237 p = 1 := by simpa only [d181238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24502 p hg
    simpa only [d181238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24504 (p : Pattern) (guard : d181239 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181218 p = 1 := by simpa only [d181239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24475 p hg
    simpa only [d181239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181238 p = 1 := by simpa only [d181239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24503 p hg
    simpa only [d181239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24505 (p : Pattern) (guard : d181240 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181239 p = 1 := by simpa only [d181240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24504 p hg
    simpa only [d181240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24506 (p : Pattern) (guard : d181241 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181240 p = 1 := by simpa only [d181241, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24505 p hg
    simpa only [d181241, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181241, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181241, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24507 (p : Pattern) (guard : d181242 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181242, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181242, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181241 p = 1 := by simpa only [d181242, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24506 p hg
    simpa only [d181242, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24508 (p : Pattern) (guard : d181243 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181237 p = 1 := by simpa only [d181243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24502 p hg
    simpa only [d181243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24509 (p : Pattern) (guard : d181244 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181238 p = 1 := by simpa only [d181244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24503 p hg
    simpa only [d181244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181243 p = 1 := by simpa only [d181244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24508 p hg
    simpa only [d181244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24510 (p : Pattern) (guard : d181245 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181244 p = 1 := by simpa only [d181245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24509 p hg
    simpa only [d181245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24511 (p : Pattern) (guard : d181246 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181245 p = 1 := by simpa only [d181246, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24510 p hg
    simpa only [d181246, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181246, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181246, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24512 (p : Pattern) (guard : d181247 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181247, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181247, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181246 p = 1 := by simpa only [d181247, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24511 p hg
    simpa only [d181247, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24513 (p : Pattern) (guard : d181248 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181242 p = 1 := by simpa only [d181248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24507 p hg
    simpa only [d181248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181247 p = 1 := by simpa only [d181248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24512 p hg
    simpa only [d181248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24514 (p : Pattern) (guard : d181249 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181248 p = 1 := by simpa only [d181249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24513 p hg
    simpa only [d181249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24515 (p : Pattern) (guard : d181250 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181249 p = 1 := by simpa only [d181250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24514 p hg
    simpa only [d181250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24516 (p : Pattern) (guard : d181251 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181250 p = 1 := by simpa only [d181251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24515 p hg
    simpa only [d181251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24517 (p : Pattern) (guard : d181252 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181222 p = 1 := by simpa only [d181252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24483 p hg
    simpa only [d181252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24518 (p : Pattern) (guard : d181253 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181252 p = 1 := by simpa only [d181253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24517 p hg
    simpa only [d181253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181233 p = 1 := by simpa only [d181253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24498 p hg
    simpa only [d181253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24519 (p : Pattern) (guard : d181254 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181224 p = 1 := by simpa only [d181254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24485 p hg
    simpa only [d181254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181253 p = 1 := by simpa only [d181254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24518 p hg
    simpa only [d181254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24520 (p : Pattern) (guard : d181255 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181255, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181255, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181254 p = 1 := by simpa only [d181255, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24519 p hg
    simpa only [d181255, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24521 (p : Pattern) (guard : d181256 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181256, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181256, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181255 p = 1 := by simpa only [d181256, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24520 p hg
    simpa only [d181256, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24522 (p : Pattern) (guard : d181257 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181256 p = 1 := by simpa only [d181257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24521 p hg
    simpa only [d181257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24523 (p : Pattern) (guard : d181258 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181257 p = 1 := by simpa only [d181258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24522 p hg
    simpa only [d181258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24524 (p : Pattern) (guard : d181259 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181258 p = 1 := by simpa only [d181259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24523 p hg
    simpa only [d181259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24525 (p : Pattern) (guard : d181260 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181259 p = 1 := by simpa only [d181260, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24524 p hg
    simpa only [d181260, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181260, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181260, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24526 (p : Pattern) (guard : d181261 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181261, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181261, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181260 p = 1 := by simpa only [d181261, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24525 p hg
    simpa only [d181261, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24527 (p : Pattern) (guard : d181262 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181247 p = 1 := by simpa only [d181262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24512 p hg
    simpa only [d181262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181261 p = 1 := by simpa only [d181262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24526 p hg
    simpa only [d181262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24528 (p : Pattern) (guard : d181263 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181262 p = 1 := by simpa only [d181263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24527 p hg
    simpa only [d181263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24529 (p : Pattern) (guard : d181264 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181263 p = 1 := by simpa only [d181264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24528 p hg
    simpa only [d181264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24530 (p : Pattern) (guard : d181265 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181264 p = 1 := by simpa only [d181265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24529 p hg
    simpa only [d181265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24531 (p : Pattern) (guard : d181266 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181251 p = 1 := by simpa only [d181266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24516 p hg
    simpa only [d181266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181265 p = 1 := by simpa only [d181266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24530 p hg
    simpa only [d181266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24532 (p : Pattern) (guard : d181267 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181266 p = 1 := by simpa only [d181267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24531 p hg
    simpa only [d181267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24533 (p : Pattern) (guard : d181268 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181252 p = 1 := by simpa only [d181268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24517 p hg
    simpa only [d181268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24534 (p : Pattern) (guard : d181269 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181224 p = 1 := by simpa only [d181269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24485 p hg
    simpa only [d181269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181268 p = 1 := by simpa only [d181269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24533 p hg
    simpa only [d181269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24535 (p : Pattern) (guard : d181270 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181270, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181270, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181269 p = 1 := by simpa only [d181270, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24534 p hg
    simpa only [d181270, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24536 (p : Pattern) (guard : d181271 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181271, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181271, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181270 p = 1 := by simpa only [d181271, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24535 p hg
    simpa only [d181271, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24537 (p : Pattern) (guard : d181272 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181271 p = 1 := by simpa only [d181272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24536 p hg
    simpa only [d181272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24538 (p : Pattern) (guard : d181273 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181238 p = 1 := by simpa only [d181273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24503 p hg
    simpa only [d181273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181272 p = 1 := by simpa only [d181273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24537 p hg
    simpa only [d181273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24539 (p : Pattern) (guard : d181274 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181273 p = 1 := by simpa only [d181274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24538 p hg
    simpa only [d181274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24540 (p : Pattern) (guard : d181275 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181274 p = 1 := by simpa only [d181275, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24539 p hg
    simpa only [d181275, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181275, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181275, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24541 (p : Pattern) (guard : d181276 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181276, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181276, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181275 p = 1 := by simpa only [d181276, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24540 p hg
    simpa only [d181276, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24542 (p : Pattern) (guard : d181277 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181276 p = 1 := by simpa only [d181277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24541 p hg
    simpa only [d181277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24543 (p : Pattern) (guard : d181278 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181277 p = 1 := by simpa only [d181278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24542 p hg
    simpa only [d181278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24544 (p : Pattern) (guard : d181279 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181278 p = 1 := by simpa only [d181279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24543 p hg
    simpa only [d181279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24545 (p : Pattern) (guard : d181280 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181279 p = 1 := by simpa only [d181280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24544 p hg
    simpa only [d181280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24546 (p : Pattern) (guard : d181281 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181280 p = 1 := by simpa only [d181281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24545 p hg
    simpa only [d181281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24547 (p : Pattern) (guard : d181282 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181281 p = 1 := by simpa only [d181282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24546 p hg
    simpa only [d181282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24548 (p : Pattern) (guard : d181283 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181267 p = 1 := by simpa only [d181283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24532 p hg
    simpa only [d181283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181282 p = 1 := by simpa only [d181283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24547 p hg
    simpa only [d181283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24549 (p : Pattern) (guard : d181284 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181283 p = 1 := by simpa only [d181284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24548 p hg
    simpa only [d181284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24550 (p : Pattern) (guard : d181285 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181284 p = 1 := by simpa only [d181285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24549 p hg
    simpa only [d181285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24551 (p : Pattern) (guard : d181286 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181286, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181286, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181285 p = 1 := by simpa only [d181286, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24550 p hg
    simpa only [d181286, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24552 (p : Pattern) (guard : d181287 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181286 p = 1 := by simpa only [d181287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24551 p hg
    simpa only [d181287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24553 (p : Pattern) (guard : d181288 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181261 p = 1 := by simpa only [d181288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24526 p hg
    simpa only [d181288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24554 (p : Pattern) (guard : d181289 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181288 p = 1 := by simpa only [d181289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24553 p hg
    simpa only [d181289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24555 (p : Pattern) (guard : d181290 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181289 p = 1 := by simpa only [d181290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24554 p hg
    simpa only [d181290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24556 (p : Pattern) (guard : d181291 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181290 p = 1 := by simpa only [d181291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24555 p hg
    simpa only [d181291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24557 (p : Pattern) (guard : d181292 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181291 p = 1 := by simpa only [d181292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24556 p hg
    simpa only [d181292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24558 (p : Pattern) (guard : d181293 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181292 p = 1 := by simpa only [d181293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24557 p hg
    simpa only [d181293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24559 (p : Pattern) (guard : d181294 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181293 p = 1 := by simpa only [d181294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24558 p hg
    simpa only [d181294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24560 (p : Pattern) (guard : d181295 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181294 p = 1 := by simpa only [d181295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24559 p hg
    simpa only [d181295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24561 (p : Pattern) (guard : d181296 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181295 p = 1 := by simpa only [d181296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24560 p hg
    simpa only [d181296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24562 (p : Pattern) (guard : d181297 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181297, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181297, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181296 p = 1 := by simpa only [d181297, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24561 p hg
    simpa only [d181297, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24563 (p : Pattern) (guard : d181298 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181297 p = 1 := by simpa only [d181298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24562 p hg
    simpa only [d181298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24564 (p : Pattern) (guard : d181299 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181287 p = 1 := by simpa only [d181299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24552 p hg
    simpa only [d181299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181298 p = 1 := by simpa only [d181299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24563 p hg
    simpa only [d181299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24565 (p : Pattern) (guard : d181300 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181299 p = 1 := by simpa only [d181300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24564 p hg
    simpa only [d181300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24566 (p : Pattern) (guard : d181301 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181300 p = 1 := by simpa only [d181301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24565 p hg
    simpa only [d181301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24567 (p : Pattern) (guard : d181302 p = 1) : d48748 p ≤ (3 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181301 p = 1 := by simpa only [d181302, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24566 p hg
    simpa only [d181302, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181302, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24155 p hg
    simpa only [d181302, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24568 (p : Pattern) (guard : d181303 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181303, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24114 p hg
    simpa only [d181303, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181302 p = 1 := by simpa only [d181303, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24567 p hg
    simpa only [d181303, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24569 (p : Pattern) (guard : d181304 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181303 p = 1 := by simpa only [d181304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24568 p hg
    simpa only [d181304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24570 (p : Pattern) (guard : d181305 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181304 p = 1 := by simpa only [d181305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24569 p hg
    simpa only [d181305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24571 (p : Pattern) (guard : d181306 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181305 p = 1 := by simpa only [d181306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24570 p hg
    simpa only [d181306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24572 (p : Pattern) (guard : d181307 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181306 p = 1 := by simpa only [d181307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24571 p hg
    simpa only [d181307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24573 (p : Pattern) (guard : d181308 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181307 p = 1 := by simpa only [d181308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24572 p hg
    simpa only [d181308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24574 (p : Pattern) (guard : d181309 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181308 p = 1 := by simpa only [d181309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24573 p hg
    simpa only [d181309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24575 (p : Pattern) (guard : d181310 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181309 p = 1 := by simpa only [d181310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24574 p hg
    simpa only [d181310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24576 (p : Pattern) (guard : d181311 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181310 p = 1 := by simpa only [d181311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24575 p hg
    simpa only [d181311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24577 (p : Pattern) (guard : d181312 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d181186 p = 1 := by simpa only [d181312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24427 p hg
    simpa only [d181312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181311 p = 1 := by simpa only [d181312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24576 p hg
    simpa only [d181312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24578 (p : Pattern) (guard : d1853 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24579 (p : Pattern) (guard : d19223 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1853 p = 1 := by simpa only [d19223, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24578 p hg
    simpa only [d19223, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19223, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19223, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24580 (p : Pattern) (guard : d181313 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19223 p = 1 := by simpa only [d181313, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24579 p hg
    simpa only [d181313, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181313, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181313, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24581 (p : Pattern) (guard : d181314 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181313 p = 1 := by simpa only [d181314, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24580 p hg
    simpa only [d181314, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181314, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181314, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24582 (p : Pattern) (guard : d17004 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24583 (p : Pattern) (guard : d19226 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17004 p = 1 := by simpa only [d19226, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24582 p hg
    simpa only [d19226, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19226, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19226, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24584 (p : Pattern) (guard : d181315 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19226 p = 1 := by simpa only [d181315, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24583 p hg
    simpa only [d181315, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181315, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181315, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24585 (p : Pattern) (guard : d181316 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181315 p = 1 := by simpa only [d181316, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24584 p hg
    simpa only [d181316, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181316, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181316, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24586 (p : Pattern) (guard : d181317 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181314 p = 1 := by simpa only [d181317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24581 p hg
    simpa only [d181317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181316 p = 1 := by simpa only [d181317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24585 p hg
    simpa only [d181317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24587 (p : Pattern) (guard : d15380 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24588 (p : Pattern) (guard : d19230 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15380 p = 1 := by simpa only [d19230, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24587 p hg
    simpa only [d19230, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19230, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19230, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24589 (p : Pattern) (guard : d181318 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19230 p = 1 := by simpa only [d181318, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24588 p hg
    simpa only [d181318, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181318, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181318, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24590 (p : Pattern) (guard : d181319 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181318 p = 1 := by simpa only [d181319, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24589 p hg
    simpa only [d181319, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181319, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181319, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24591 (p : Pattern) (guard : d15387 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24592 (p : Pattern) (guard : d19233 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15387 p = 1 := by simpa only [d19233, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24591 p hg
    simpa only [d19233, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19233, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19233, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24593 (p : Pattern) (guard : d181320 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19233 p = 1 := by simpa only [d181320, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24592 p hg
    simpa only [d181320, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181320, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181320, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24594 (p : Pattern) (guard : d181321 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181320 p = 1 := by simpa only [d181321, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24593 p hg
    simpa only [d181321, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181321, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181321, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24595 (p : Pattern) (guard : d181322 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181319 p = 1 := by simpa only [d181322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24590 p hg
    simpa only [d181322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181321 p = 1 := by simpa only [d181322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24594 p hg
    simpa only [d181322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24596 (p : Pattern) (guard : d181323 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181317 p = 1 := by simpa only [d181323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24586 p hg
    simpa only [d181323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181322 p = 1 := by simpa only [d181323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24595 p hg
    simpa only [d181323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24597 (p : Pattern) (guard : d1857 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24598 (p : Pattern) (guard : d19238 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1857 p = 1 := by simpa only [d19238, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24597 p hg
    simpa only [d19238, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19238, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19238, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24599 (p : Pattern) (guard : d181324 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19238 p = 1 := by simpa only [d181324, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24598 p hg
    simpa only [d181324, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181324, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181324, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24600 (p : Pattern) (guard : d181325 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181324 p = 1 := by simpa only [d181325, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24599 p hg
    simpa only [d181325, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181325, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181325, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24601 (p : Pattern) (guard : d17011 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24602 (p : Pattern) (guard : d19241 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17011 p = 1 := by simpa only [d19241, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24601 p hg
    simpa only [d19241, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19241, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19241, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24603 (p : Pattern) (guard : d181326 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19241 p = 1 := by simpa only [d181326, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24602 p hg
    simpa only [d181326, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181326, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181326, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24604 (p : Pattern) (guard : d181327 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181326 p = 1 := by simpa only [d181327, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24603 p hg
    simpa only [d181327, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181327, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181327, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24605 (p : Pattern) (guard : d181328 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181325 p = 1 := by simpa only [d181328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24600 p hg
    simpa only [d181328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181327 p = 1 := by simpa only [d181328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24604 p hg
    simpa only [d181328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24606 (p : Pattern) (guard : d15397 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24607 (p : Pattern) (guard : d19245 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15397 p = 1 := by simpa only [d19245, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24606 p hg
    simpa only [d19245, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19245, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19245, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24608 (p : Pattern) (guard : d181329 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19245 p = 1 := by simpa only [d181329, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24607 p hg
    simpa only [d181329, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181329, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181329, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24609 (p : Pattern) (guard : d181330 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181329 p = 1 := by simpa only [d181330, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24608 p hg
    simpa only [d181330, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181330, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181330, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24610 (p : Pattern) (guard : d181331 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181321 p = 1 := by simpa only [d181331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24594 p hg
    simpa only [d181331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181330 p = 1 := by simpa only [d181331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24609 p hg
    simpa only [d181331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24611 (p : Pattern) (guard : d181332 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181328 p = 1 := by simpa only [d181332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24605 p hg
    simpa only [d181332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181331 p = 1 := by simpa only [d181332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24610 p hg
    simpa only [d181332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24612 (p : Pattern) (guard : d181333 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181323 p = 1 := by simpa only [d181333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24596 p hg
    simpa only [d181333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181332 p = 1 := by simpa only [d181333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24611 p hg
    simpa only [d181333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24613 (p : Pattern) (guard : d181334 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181334, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181334, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181333 p = 1 := by simpa only [d181334, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24612 p hg
    simpa only [d181334, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24614 (p : Pattern) (guard : d181335 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181335, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181335, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181334 p = 1 := by simpa only [d181335, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24613 p hg
    simpa only [d181335, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24615 (p : Pattern) (guard : d13486 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24616 (p : Pattern) (guard : d19253 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13486 p = 1 := by simpa only [d19253, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24615 p hg
    simpa only [d19253, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19253, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19253, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24617 (p : Pattern) (guard : d181336 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19253 p = 1 := by simpa only [d181336, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24616 p hg
    simpa only [d181336, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181336, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181336, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24618 (p : Pattern) (guard : d181337 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181336 p = 1 := by simpa only [d181337, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24617 p hg
    simpa only [d181337, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181337, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181337, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24619 (p : Pattern) (guard : d181338 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181337 p = 1 := by simpa only [d181338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24618 p hg
    simpa only [d181338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181330 p = 1 := by simpa only [d181338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24609 p hg
    simpa only [d181338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24620 (p : Pattern) (guard : d181339 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181330 p = 1 := by simpa only [d181339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24609 p hg
    simpa only [d181339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24621 (p : Pattern) (guard : d181340 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181338 p = 1 := by simpa only [d181340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24619 p hg
    simpa only [d181340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181339 p = 1 := by simpa only [d181340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24620 p hg
    simpa only [d181340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24622 (p : Pattern) (guard : d181341 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181332 p = 1 := by simpa only [d181341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24611 p hg
    simpa only [d181341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181340 p = 1 := by simpa only [d181341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24621 p hg
    simpa only [d181341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24623 (p : Pattern) (guard : d181342 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181342, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181342, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181341 p = 1 := by simpa only [d181342, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24622 p hg
    simpa only [d181342, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24624 (p : Pattern) (guard : d181343 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181343, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181343, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181342 p = 1 := by simpa only [d181343, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24623 p hg
    simpa only [d181343, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24625 (p : Pattern) (guard : d181344 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181335 p = 1 := by simpa only [d181344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24614 p hg
    simpa only [d181344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181343 p = 1 := by simpa only [d181344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24624 p hg
    simpa only [d181344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24626 (p : Pattern) (guard : d1862 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24627 (p : Pattern) (guard : d19263 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1862 p = 1 := by simpa only [d19263, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24626 p hg
    simpa only [d19263, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19263, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19263, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24628 (p : Pattern) (guard : d181345 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19263 p = 1 := by simpa only [d181345, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24627 p hg
    simpa only [d181345, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181345, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181345, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24629 (p : Pattern) (guard : d181346 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181345 p = 1 := by simpa only [d181346, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24628 p hg
    simpa only [d181346, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181346, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181346, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24630 (p : Pattern) (guard : d17027 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24631 (p : Pattern) (guard : d19266 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17027 p = 1 := by simpa only [d19266, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24630 p hg
    simpa only [d19266, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19266, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19266, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24632 (p : Pattern) (guard : d181347 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19266 p = 1 := by simpa only [d181347, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24631 p hg
    simpa only [d181347, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181347, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181347, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24633 (p : Pattern) (guard : d181348 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181347 p = 1 := by simpa only [d181348, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24632 p hg
    simpa only [d181348, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181348, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181348, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24634 (p : Pattern) (guard : d181349 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181346 p = 1 := by simpa only [d181349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24629 p hg
    simpa only [d181349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181348 p = 1 := by simpa only [d181349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24633 p hg
    simpa only [d181349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24635 (p : Pattern) (guard : d181350 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181349 p = 1 := by simpa only [d181350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24634 p hg
    simpa only [d181350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181339 p = 1 := by simpa only [d181350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24620 p hg
    simpa only [d181350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24636 (p : Pattern) (guard : d181351 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181332 p = 1 := by simpa only [d181351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24611 p hg
    simpa only [d181351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181350 p = 1 := by simpa only [d181351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24635 p hg
    simpa only [d181351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24637 (p : Pattern) (guard : d181352 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181352, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181352, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181351 p = 1 := by simpa only [d181352, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24636 p hg
    simpa only [d181352, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24638 (p : Pattern) (guard : d181353 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181353, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181353, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181352 p = 1 := by simpa only [d181353, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24637 p hg
    simpa only [d181353, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24639 (p : Pattern) (guard : d6496 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24640 (p : Pattern) (guard : d19274 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6496 p = 1 := by simpa only [d19274, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24639 p hg
    simpa only [d19274, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19274, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19274, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24641 (p : Pattern) (guard : d181354 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19274 p = 1 := by simpa only [d181354, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24640 p hg
    simpa only [d181354, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181354, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181354, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24642 (p : Pattern) (guard : d181355 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181354 p = 1 := by simpa only [d181355, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24641 p hg
    simpa only [d181355, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181355, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181355, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24643 (p : Pattern) (guard : d181356 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181355 p = 1 := by simpa only [d181356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24642 p hg
    simpa only [d181356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24644 (p : Pattern) (guard : d15412 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24645 (p : Pattern) (guard : d19278 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15412 p = 1 := by simpa only [d19278, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24644 p hg
    simpa only [d19278, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19278, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19278, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24646 (p : Pattern) (guard : d181357 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19278 p = 1 := by simpa only [d181357, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24645 p hg
    simpa only [d181357, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181357, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181357, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24647 (p : Pattern) (guard : d181358 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181357 p = 1 := by simpa only [d181358, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24646 p hg
    simpa only [d181358, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181358, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181358, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24648 (p : Pattern) (guard : d181359 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181358 p = 1 := by simpa only [d181359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24647 p hg
    simpa only [d181359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24649 (p : Pattern) (guard : d181360 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181356 p = 1 := by simpa only [d181360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24643 p hg
    simpa only [d181360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181359 p = 1 := by simpa only [d181360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24648 p hg
    simpa only [d181360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24650 (p : Pattern) (guard : d181361 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181350 p = 1 := by simpa only [d181361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24635 p hg
    simpa only [d181361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181360 p = 1 := by simpa only [d181361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24649 p hg
    simpa only [d181361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24651 (p : Pattern) (guard : d181362 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181362, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181362, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181361 p = 1 := by simpa only [d181362, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24650 p hg
    simpa only [d181362, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24652 (p : Pattern) (guard : d181363 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181363, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181363, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181362 p = 1 := by simpa only [d181363, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24651 p hg
    simpa only [d181363, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24653 (p : Pattern) (guard : d181364 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181353 p = 1 := by simpa only [d181364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24638 p hg
    simpa only [d181364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181363 p = 1 := by simpa only [d181364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24652 p hg
    simpa only [d181364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24654 (p : Pattern) (guard : d181365 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181344 p = 1 := by simpa only [d181365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24625 p hg
    simpa only [d181365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181364 p = 1 := by simpa only [d181365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24653 p hg
    simpa only [d181365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24655 (p : Pattern) (guard : d181366 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181365 p = 1 := by simpa only [d181366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24654 p hg
    simpa only [d181366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24656 (p : Pattern) (guard : d181367 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181366 p = 1 := by simpa only [d181367, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24655 p hg
    simpa only [d181367, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181367, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181367, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24657 (p : Pattern) (guard : d181368 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181368, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181368, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181367 p = 1 := by simpa only [d181368, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24656 p hg
    simpa only [d181368, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24658 (p : Pattern) (guard : d181369 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181363 p = 1 := by simpa only [d181369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24652 p hg
    simpa only [d181369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24659 (p : Pattern) (guard : d181370 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181364 p = 1 := by simpa only [d181370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24653 p hg
    simpa only [d181370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181369 p = 1 := by simpa only [d181370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24658 p hg
    simpa only [d181370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24660 (p : Pattern) (guard : d181371 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181370 p = 1 := by simpa only [d181371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24659 p hg
    simpa only [d181371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24661 (p : Pattern) (guard : d181372 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181371 p = 1 := by simpa only [d181372, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24660 p hg
    simpa only [d181372, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181372, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181372, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24662 (p : Pattern) (guard : d181373 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181373, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181373, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181372 p = 1 := by simpa only [d181373, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24661 p hg
    simpa only [d181373, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24663 (p : Pattern) (guard : d181374 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181368 p = 1 := by simpa only [d181374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24657 p hg
    simpa only [d181374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181373 p = 1 := by simpa only [d181374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24662 p hg
    simpa only [d181374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24664 (p : Pattern) (guard : d181375 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181374 p = 1 := by simpa only [d181375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24663 p hg
    simpa only [d181375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24665 (p : Pattern) (guard : d181376 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181375 p = 1 := by simpa only [d181376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24664 p hg
    simpa only [d181376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24666 (p : Pattern) (guard : d181377 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181376 p = 1 := by simpa only [d181377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24665 p hg
    simpa only [d181377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24667 (p : Pattern) (guard : d1868 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24668 (p : Pattern) (guard : d19313 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1868 p = 1 := by simpa only [d19313, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24667 p hg
    simpa only [d19313, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19313, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19313, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24669 (p : Pattern) (guard : d181378 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19313 p = 1 := by simpa only [d181378, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24668 p hg
    simpa only [d181378, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181378, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181378, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24670 (p : Pattern) (guard : d181379 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181378 p = 1 := by simpa only [d181379, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24669 p hg
    simpa only [d181379, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181379, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181379, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24671 (p : Pattern) (guard : d181380 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181379 p = 1 := by simpa only [d181380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24670 p hg
    simpa only [d181380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24672 (p : Pattern) (guard : d181381 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181380 p = 1 := by simpa only [d181381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24671 p hg
    simpa only [d181381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181359 p = 1 := by simpa only [d181381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24648 p hg
    simpa only [d181381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24673 (p : Pattern) (guard : d181382 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181350 p = 1 := by simpa only [d181382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24635 p hg
    simpa only [d181382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181381 p = 1 := by simpa only [d181382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24672 p hg
    simpa only [d181382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24674 (p : Pattern) (guard : d181383 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181383, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181383, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181382 p = 1 := by simpa only [d181383, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24673 p hg
    simpa only [d181383, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24675 (p : Pattern) (guard : d181384 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181384, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181384, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181383 p = 1 := by simpa only [d181384, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24674 p hg
    simpa only [d181384, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24676 (p : Pattern) (guard : d181385 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181384 p = 1 := by simpa only [d181385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24675 p hg
    simpa only [d181385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24677 (p : Pattern) (guard : d181386 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181385 p = 1 := by simpa only [d181386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24676 p hg
    simpa only [d181386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24678 (p : Pattern) (guard : d181387 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181386 p = 1 := by simpa only [d181387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24677 p hg
    simpa only [d181387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24679 (p : Pattern) (guard : d181388 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181387 p = 1 := by simpa only [d181388, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24678 p hg
    simpa only [d181388, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181388, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181388, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24680 (p : Pattern) (guard : d181389 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181389, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181389, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181388 p = 1 := by simpa only [d181389, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24679 p hg
    simpa only [d181389, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24681 (p : Pattern) (guard : d181390 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181373 p = 1 := by simpa only [d181390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24662 p hg
    simpa only [d181390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181389 p = 1 := by simpa only [d181390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24680 p hg
    simpa only [d181390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24682 (p : Pattern) (guard : d181391 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181390 p = 1 := by simpa only [d181391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24681 p hg
    simpa only [d181391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24683 (p : Pattern) (guard : d181392 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181391 p = 1 := by simpa only [d181392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24682 p hg
    simpa only [d181392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24684 (p : Pattern) (guard : d181393 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181392 p = 1 := by simpa only [d181393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24683 p hg
    simpa only [d181393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24685 (p : Pattern) (guard : d181394 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181377 p = 1 := by simpa only [d181394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24666 p hg
    simpa only [d181394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181393 p = 1 := by simpa only [d181394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24684 p hg
    simpa only [d181394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24686 (p : Pattern) (guard : d181395 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181394 p = 1 := by simpa only [d181395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24685 p hg
    simpa only [d181395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24687 (p : Pattern) (guard : d181396 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181380 p = 1 := by simpa only [d181396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24671 p hg
    simpa only [d181396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24688 (p : Pattern) (guard : d181397 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181350 p = 1 := by simpa only [d181397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24635 p hg
    simpa only [d181397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181396 p = 1 := by simpa only [d181397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24687 p hg
    simpa only [d181397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24689 (p : Pattern) (guard : d181398 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181398, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181398, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181397 p = 1 := by simpa only [d181398, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24688 p hg
    simpa only [d181398, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24690 (p : Pattern) (guard : d181399 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181399, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181399, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181398 p = 1 := by simpa only [d181399, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24689 p hg
    simpa only [d181399, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24691 (p : Pattern) (guard : d181400 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181399 p = 1 := by simpa only [d181400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24690 p hg
    simpa only [d181400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24692 (p : Pattern) (guard : d181401 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181364 p = 1 := by simpa only [d181401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24653 p hg
    simpa only [d181401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181400 p = 1 := by simpa only [d181401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24691 p hg
    simpa only [d181401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24693 (p : Pattern) (guard : d181402 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181401 p = 1 := by simpa only [d181402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24692 p hg
    simpa only [d181402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24694 (p : Pattern) (guard : d181403 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181402 p = 1 := by simpa only [d181403, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24693 p hg
    simpa only [d181403, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181403, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181403, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24695 (p : Pattern) (guard : d181404 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181404, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181404, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181403 p = 1 := by simpa only [d181404, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24694 p hg
    simpa only [d181404, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24696 (p : Pattern) (guard : d181405 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181404 p = 1 := by simpa only [d181405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24695 p hg
    simpa only [d181405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24697 (p : Pattern) (guard : d181406 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181405 p = 1 := by simpa only [d181406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24696 p hg
    simpa only [d181406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24698 (p : Pattern) (guard : d181407 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181406 p = 1 := by simpa only [d181407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24697 p hg
    simpa only [d181407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24699 (p : Pattern) (guard : d181408 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181407 p = 1 := by simpa only [d181408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24698 p hg
    simpa only [d181408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24700 (p : Pattern) (guard : d181409 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181408 p = 1 := by simpa only [d181409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24699 p hg
    simpa only [d181409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24701 (p : Pattern) (guard : d181410 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181409 p = 1 := by simpa only [d181410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24700 p hg
    simpa only [d181410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24702 (p : Pattern) (guard : d181411 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181395 p = 1 := by simpa only [d181411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24686 p hg
    simpa only [d181411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181410 p = 1 := by simpa only [d181411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24701 p hg
    simpa only [d181411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24703 (p : Pattern) (guard : d181412 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181411 p = 1 := by simpa only [d181412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24702 p hg
    simpa only [d181412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24704 (p : Pattern) (guard : d181413 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181412 p = 1 := by simpa only [d181413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24703 p hg
    simpa only [d181413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24705 (p : Pattern) (guard : d181414 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181414, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181414, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181413 p = 1 := by simpa only [d181414, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24704 p hg
    simpa only [d181414, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24706 (p : Pattern) (guard : d181415 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181414 p = 1 := by simpa only [d181415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24705 p hg
    simpa only [d181415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24707 (p : Pattern) (guard : d181416 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181389 p = 1 := by simpa only [d181416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24680 p hg
    simpa only [d181416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24708 (p : Pattern) (guard : d181417 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181416 p = 1 := by simpa only [d181417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24707 p hg
    simpa only [d181417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24709 (p : Pattern) (guard : d181418 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181417 p = 1 := by simpa only [d181418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24708 p hg
    simpa only [d181418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24710 (p : Pattern) (guard : d181419 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181418 p = 1 := by simpa only [d181419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24709 p hg
    simpa only [d181419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24711 (p : Pattern) (guard : d181420 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181419 p = 1 := by simpa only [d181420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24710 p hg
    simpa only [d181420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24712 (p : Pattern) (guard : d181421 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181420 p = 1 := by simpa only [d181421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24711 p hg
    simpa only [d181421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24713 (p : Pattern) (guard : d181422 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181421 p = 1 := by simpa only [d181422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24712 p hg
    simpa only [d181422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24714 (p : Pattern) (guard : d181423 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181422 p = 1 := by simpa only [d181423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24713 p hg
    simpa only [d181423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24715 (p : Pattern) (guard : d181424 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181423 p = 1 := by simpa only [d181424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24714 p hg
    simpa only [d181424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24716 (p : Pattern) (guard : d181425 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181425, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181425, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181424 p = 1 := by simpa only [d181425, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24715 p hg
    simpa only [d181425, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24717 (p : Pattern) (guard : d181426 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181425 p = 1 := by simpa only [d181426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24716 p hg
    simpa only [d181426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24718 (p : Pattern) (guard : d181427 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181415 p = 1 := by simpa only [d181427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24706 p hg
    simpa only [d181427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181426 p = 1 := by simpa only [d181427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24717 p hg
    simpa only [d181427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24719 (p : Pattern) (guard : d181428 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181427 p = 1 := by simpa only [d181428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24718 p hg
    simpa only [d181428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24720 (p : Pattern) (guard : d181429 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181428 p = 1 := by simpa only [d181429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24719 p hg
    simpa only [d181429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24721 (p : Pattern) (guard : d181430 p = 1) : d48748 p ≤ (3 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181429 p = 1 := by simpa only [d181430, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24720 p hg
    simpa only [d181430, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181430, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24155 p hg
    simpa only [d181430, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24722 (p : Pattern) (guard : d181431 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181431, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24114 p hg
    simpa only [d181431, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181430 p = 1 := by simpa only [d181431, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24721 p hg
    simpa only [d181431, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24723 (p : Pattern) (guard : d181432 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181431 p = 1 := by simpa only [d181432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24722 p hg
    simpa only [d181432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24724 (p : Pattern) (guard : d181433 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181432 p = 1 := by simpa only [d181433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24723 p hg
    simpa only [d181433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24725 (p : Pattern) (guard : d181434 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181433 p = 1 := by simpa only [d181434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24724 p hg
    simpa only [d181434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24726 (p : Pattern) (guard : d181435 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181434 p = 1 := by simpa only [d181435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24725 p hg
    simpa only [d181435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24727 (p : Pattern) (guard : d181436 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181435 p = 1 := by simpa only [d181436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24726 p hg
    simpa only [d181436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24728 (p : Pattern) (guard : d181437 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181436 p = 1 := by simpa only [d181437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24727 p hg
    simpa only [d181437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24729 (p : Pattern) (guard : d181438 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181437 p = 1 := by simpa only [d181438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24728 p hg
    simpa only [d181438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24730 (p : Pattern) (guard : d181439 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181438 p = 1 := by simpa only [d181439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24729 p hg
    simpa only [d181439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24731 (p : Pattern) (guard : d181440 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181439 p = 1 := by simpa only [d181440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24730 p hg
    simpa only [d181440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24732 (p : Pattern) (guard : d181441 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d181312 p = 1 := by simpa only [d181441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24577 p hg
    simpa only [d181441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181440 p = 1 := by simpa only [d181441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24731 p hg
    simpa only [d181441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24733 (p : Pattern) (guard : d2331 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24734 (p : Pattern) (guard : d19462 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2331 p = 1 := by simpa only [d19462, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24733 p hg
    simpa only [d19462, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19462, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19462, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24735 (p : Pattern) (guard : d181442 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19462 p = 1 := by simpa only [d181442, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24734 p hg
    simpa only [d181442, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181442, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181442, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24736 (p : Pattern) (guard : d181443 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181442 p = 1 := by simpa only [d181443, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24735 p hg
    simpa only [d181443, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181443, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181443, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24737 (p : Pattern) (guard : d17369 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24738 (p : Pattern) (guard : d19465 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17369 p = 1 := by simpa only [d19465, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24737 p hg
    simpa only [d19465, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19465, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19465, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24739 (p : Pattern) (guard : d181444 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19465 p = 1 := by simpa only [d181444, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24738 p hg
    simpa only [d181444, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181444, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181444, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24740 (p : Pattern) (guard : d181445 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181444 p = 1 := by simpa only [d181445, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24739 p hg
    simpa only [d181445, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181445, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181445, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24741 (p : Pattern) (guard : d181446 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181443 p = 1 := by simpa only [d181446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24736 p hg
    simpa only [d181446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181445 p = 1 := by simpa only [d181446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24740 p hg
    simpa only [d181446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24742 (p : Pattern) (guard : d13813 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24743 (p : Pattern) (guard : d19469 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13813 p = 1 := by simpa only [d19469, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24742 p hg
    simpa only [d19469, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19469, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19469, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24744 (p : Pattern) (guard : d181447 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19469 p = 1 := by simpa only [d181447, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24743 p hg
    simpa only [d181447, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181447, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181447, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24745 (p : Pattern) (guard : d181448 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181447 p = 1 := by simpa only [d181448, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24744 p hg
    simpa only [d181448, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181448, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181448, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24746 (p : Pattern) (guard : d181449 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181448 p = 1 := by simpa only [d181449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24745 p hg
    simpa only [d181449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24747 (p : Pattern) (guard : d181450 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181446 p = 1 := by simpa only [d181450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24741 p hg
    simpa only [d181450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181449 p = 1 := by simpa only [d181450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24746 p hg
    simpa only [d181450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24748 (p : Pattern) (guard : d2335 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24749 (p : Pattern) (guard : d19474 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2335 p = 1 := by simpa only [d19474, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24748 p hg
    simpa only [d19474, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19474, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19474, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
