import NetHack.Soko22Hazard87.Compare098
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24750 (p : Pattern) (guard : d181451 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19474 p = 1 := by simpa only [d181451, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24749 p hg
    simpa only [d181451, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181451, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181451, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24751 (p : Pattern) (guard : d181452 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181451 p = 1 := by simpa only [d181452, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24750 p hg
    simpa only [d181452, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181452, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181452, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24752 (p : Pattern) (guard : d17376 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24753 (p : Pattern) (guard : d19477 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17376 p = 1 := by simpa only [d19477, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24752 p hg
    simpa only [d19477, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19477, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19477, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24754 (p : Pattern) (guard : d181453 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19477 p = 1 := by simpa only [d181453, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24753 p hg
    simpa only [d181453, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181453, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181453, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24755 (p : Pattern) (guard : d181454 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181453 p = 1 := by simpa only [d181454, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24754 p hg
    simpa only [d181454, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181454, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181454, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24756 (p : Pattern) (guard : d181455 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181452 p = 1 := by simpa only [d181455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24751 p hg
    simpa only [d181455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181454 p = 1 := by simpa only [d181455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24755 p hg
    simpa only [d181455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24757 (p : Pattern) (guard : d15775 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24758 (p : Pattern) (guard : d19481 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15775 p = 1 := by simpa only [d19481, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24757 p hg
    simpa only [d19481, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19481, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19481, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24759 (p : Pattern) (guard : d181456 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19481 p = 1 := by simpa only [d181456, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24758 p hg
    simpa only [d181456, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181456, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181456, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24760 (p : Pattern) (guard : d181457 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181456 p = 1 := by simpa only [d181457, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24759 p hg
    simpa only [d181457, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181457, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181457, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24761 (p : Pattern) (guard : d181458 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181448 p = 1 := by simpa only [d181458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24745 p hg
    simpa only [d181458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181457 p = 1 := by simpa only [d181458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24760 p hg
    simpa only [d181458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24762 (p : Pattern) (guard : d181459 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181455 p = 1 := by simpa only [d181459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24756 p hg
    simpa only [d181459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181458 p = 1 := by simpa only [d181459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24761 p hg
    simpa only [d181459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24763 (p : Pattern) (guard : d181460 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181450 p = 1 := by simpa only [d181460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24747 p hg
    simpa only [d181460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181459 p = 1 := by simpa only [d181460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24762 p hg
    simpa only [d181460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24764 (p : Pattern) (guard : d181461 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181461, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181461, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181460 p = 1 := by simpa only [d181461, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24763 p hg
    simpa only [d181461, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24765 (p : Pattern) (guard : d181462 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181462, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181462, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181461 p = 1 := by simpa only [d181462, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24764 p hg
    simpa only [d181462, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24766 (p : Pattern) (guard : d181463 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181457 p = 1 := by simpa only [d181463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24760 p hg
    simpa only [d181463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24767 (p : Pattern) (guard : d181464 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181458 p = 1 := by simpa only [d181464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24761 p hg
    simpa only [d181464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181463 p = 1 := by simpa only [d181464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24766 p hg
    simpa only [d181464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24768 (p : Pattern) (guard : d181465 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181459 p = 1 := by simpa only [d181465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24762 p hg
    simpa only [d181465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181464 p = 1 := by simpa only [d181465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24767 p hg
    simpa only [d181465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24769 (p : Pattern) (guard : d181466 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181466, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181466, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181465 p = 1 := by simpa only [d181466, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24768 p hg
    simpa only [d181466, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24770 (p : Pattern) (guard : d181467 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181467, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181467, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181466 p = 1 := by simpa only [d181467, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24769 p hg
    simpa only [d181467, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24771 (p : Pattern) (guard : d181468 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181462 p = 1 := by simpa only [d181468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24765 p hg
    simpa only [d181468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181467 p = 1 := by simpa only [d181468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24770 p hg
    simpa only [d181468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24772 (p : Pattern) (guard : d2340 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24773 (p : Pattern) (guard : d19495 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2340 p = 1 := by simpa only [d19495, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24772 p hg
    simpa only [d19495, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19495, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19495, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24774 (p : Pattern) (guard : d181469 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19495 p = 1 := by simpa only [d181469, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24773 p hg
    simpa only [d181469, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181469, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181469, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24775 (p : Pattern) (guard : d181470 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181469 p = 1 := by simpa only [d181470, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24774 p hg
    simpa only [d181470, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181470, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181470, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24776 (p : Pattern) (guard : d17391 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24777 (p : Pattern) (guard : d19498 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17391 p = 1 := by simpa only [d19498, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24776 p hg
    simpa only [d19498, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19498, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19498, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24778 (p : Pattern) (guard : d181471 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19498 p = 1 := by simpa only [d181471, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24777 p hg
    simpa only [d181471, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181471, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181471, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24779 (p : Pattern) (guard : d181472 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181471 p = 1 := by simpa only [d181472, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24778 p hg
    simpa only [d181472, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181472, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181472, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24780 (p : Pattern) (guard : d181473 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181470 p = 1 := by simpa only [d181473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24775 p hg
    simpa only [d181473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181472 p = 1 := by simpa only [d181473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24779 p hg
    simpa only [d181473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24781 (p : Pattern) (guard : d181474 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181473 p = 1 := by simpa only [d181474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24780 p hg
    simpa only [d181474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181463 p = 1 := by simpa only [d181474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24766 p hg
    simpa only [d181474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24782 (p : Pattern) (guard : d181475 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181459 p = 1 := by simpa only [d181475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24762 p hg
    simpa only [d181475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181474 p = 1 := by simpa only [d181475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24781 p hg
    simpa only [d181475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24783 (p : Pattern) (guard : d181476 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181476, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181476, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181475 p = 1 := by simpa only [d181476, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24782 p hg
    simpa only [d181476, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24784 (p : Pattern) (guard : d181477 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181477, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181477, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181476 p = 1 := by simpa only [d181477, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24783 p hg
    simpa only [d181477, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24785 (p : Pattern) (guard : d6643 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24786 (p : Pattern) (guard : d19506 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6643 p = 1 := by simpa only [d19506, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24785 p hg
    simpa only [d19506, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19506, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19506, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24787 (p : Pattern) (guard : d181478 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19506 p = 1 := by simpa only [d181478, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24786 p hg
    simpa only [d181478, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181478, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181478, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24788 (p : Pattern) (guard : d181479 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181478 p = 1 := by simpa only [d181479, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24787 p hg
    simpa only [d181479, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181479, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181479, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24789 (p : Pattern) (guard : d181480 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181479 p = 1 := by simpa only [d181480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24788 p hg
    simpa only [d181480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24790 (p : Pattern) (guard : d15790 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24791 (p : Pattern) (guard : d19510 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15790 p = 1 := by simpa only [d19510, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24790 p hg
    simpa only [d19510, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19510, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19510, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24792 (p : Pattern) (guard : d181481 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19510 p = 1 := by simpa only [d181481, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24791 p hg
    simpa only [d181481, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181481, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181481, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24793 (p : Pattern) (guard : d181482 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181481 p = 1 := by simpa only [d181482, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24792 p hg
    simpa only [d181482, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181482, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181482, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24794 (p : Pattern) (guard : d181483 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181482 p = 1 := by simpa only [d181483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24793 p hg
    simpa only [d181483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24795 (p : Pattern) (guard : d181484 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181480 p = 1 := by simpa only [d181484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24789 p hg
    simpa only [d181484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181483 p = 1 := by simpa only [d181484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24794 p hg
    simpa only [d181484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24796 (p : Pattern) (guard : d181485 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181474 p = 1 := by simpa only [d181485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24781 p hg
    simpa only [d181485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181484 p = 1 := by simpa only [d181485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24795 p hg
    simpa only [d181485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24797 (p : Pattern) (guard : d181486 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181486, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181486, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181485 p = 1 := by simpa only [d181486, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24796 p hg
    simpa only [d181486, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24798 (p : Pattern) (guard : d181487 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181487, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181487, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181486 p = 1 := by simpa only [d181487, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24797 p hg
    simpa only [d181487, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24799 (p : Pattern) (guard : d181488 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181477 p = 1 := by simpa only [d181488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24784 p hg
    simpa only [d181488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181487 p = 1 := by simpa only [d181488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24798 p hg
    simpa only [d181488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24800 (p : Pattern) (guard : d181489 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181468 p = 1 := by simpa only [d181489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24771 p hg
    simpa only [d181489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181488 p = 1 := by simpa only [d181489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24799 p hg
    simpa only [d181489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24801 (p : Pattern) (guard : d181490 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181489 p = 1 := by simpa only [d181490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24800 p hg
    simpa only [d181490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24802 (p : Pattern) (guard : d181491 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181490 p = 1 := by simpa only [d181491, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24801 p hg
    simpa only [d181491, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181491, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181491, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24803 (p : Pattern) (guard : d181492 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181492, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181492, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181491 p = 1 := by simpa only [d181492, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24802 p hg
    simpa only [d181492, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24804 (p : Pattern) (guard : d181493 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181487 p = 1 := by simpa only [d181493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24798 p hg
    simpa only [d181493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24805 (p : Pattern) (guard : d181494 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181488 p = 1 := by simpa only [d181494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24799 p hg
    simpa only [d181494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181493 p = 1 := by simpa only [d181494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24804 p hg
    simpa only [d181494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24806 (p : Pattern) (guard : d181495 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181494 p = 1 := by simpa only [d181495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24805 p hg
    simpa only [d181495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24807 (p : Pattern) (guard : d181496 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181495 p = 1 := by simpa only [d181496, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24806 p hg
    simpa only [d181496, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181496, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181496, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24808 (p : Pattern) (guard : d181497 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181497, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181497, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181496 p = 1 := by simpa only [d181497, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24807 p hg
    simpa only [d181497, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24809 (p : Pattern) (guard : d181498 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181492 p = 1 := by simpa only [d181498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24803 p hg
    simpa only [d181498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181497 p = 1 := by simpa only [d181498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24808 p hg
    simpa only [d181498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24810 (p : Pattern) (guard : d181499 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181498 p = 1 := by simpa only [d181499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24809 p hg
    simpa only [d181499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24811 (p : Pattern) (guard : d181500 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181499 p = 1 := by simpa only [d181500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24810 p hg
    simpa only [d181500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24812 (p : Pattern) (guard : d181501 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181500 p = 1 := by simpa only [d181501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24811 p hg
    simpa only [d181501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24813 (p : Pattern) (guard : d2346 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24814 (p : Pattern) (guard : d19545 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2346 p = 1 := by simpa only [d19545, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24813 p hg
    simpa only [d19545, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19545, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19545, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24815 (p : Pattern) (guard : d181502 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19545 p = 1 := by simpa only [d181502, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24814 p hg
    simpa only [d181502, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181502, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181502, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24816 (p : Pattern) (guard : d181503 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181502 p = 1 := by simpa only [d181503, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24815 p hg
    simpa only [d181503, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181503, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181503, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24817 (p : Pattern) (guard : d181504 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181503 p = 1 := by simpa only [d181504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24816 p hg
    simpa only [d181504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24818 (p : Pattern) (guard : d181505 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181504 p = 1 := by simpa only [d181505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24817 p hg
    simpa only [d181505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181483 p = 1 := by simpa only [d181505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24794 p hg
    simpa only [d181505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24819 (p : Pattern) (guard : d181506 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181474 p = 1 := by simpa only [d181506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24781 p hg
    simpa only [d181506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181505 p = 1 := by simpa only [d181506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24818 p hg
    simpa only [d181506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24820 (p : Pattern) (guard : d181507 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181507, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181507, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181506 p = 1 := by simpa only [d181507, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24819 p hg
    simpa only [d181507, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24821 (p : Pattern) (guard : d181508 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181508, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181508, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181507 p = 1 := by simpa only [d181508, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24820 p hg
    simpa only [d181508, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24822 (p : Pattern) (guard : d181509 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181508 p = 1 := by simpa only [d181509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24821 p hg
    simpa only [d181509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24823 (p : Pattern) (guard : d181510 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181509 p = 1 := by simpa only [d181510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24822 p hg
    simpa only [d181510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24824 (p : Pattern) (guard : d181511 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181510 p = 1 := by simpa only [d181511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24823 p hg
    simpa only [d181511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24825 (p : Pattern) (guard : d181512 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181511 p = 1 := by simpa only [d181512, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24824 p hg
    simpa only [d181512, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181512, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181512, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24826 (p : Pattern) (guard : d181513 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181513, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181513, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181512 p = 1 := by simpa only [d181513, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24825 p hg
    simpa only [d181513, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24827 (p : Pattern) (guard : d181514 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181497 p = 1 := by simpa only [d181514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24808 p hg
    simpa only [d181514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181513 p = 1 := by simpa only [d181514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24826 p hg
    simpa only [d181514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24828 (p : Pattern) (guard : d181515 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181514 p = 1 := by simpa only [d181515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24827 p hg
    simpa only [d181515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24829 (p : Pattern) (guard : d181516 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181515 p = 1 := by simpa only [d181516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24828 p hg
    simpa only [d181516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24830 (p : Pattern) (guard : d181517 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181516 p = 1 := by simpa only [d181517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24829 p hg
    simpa only [d181517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24831 (p : Pattern) (guard : d181518 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181501 p = 1 := by simpa only [d181518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24812 p hg
    simpa only [d181518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181517 p = 1 := by simpa only [d181518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24830 p hg
    simpa only [d181518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24832 (p : Pattern) (guard : d181519 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181518 p = 1 := by simpa only [d181519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24831 p hg
    simpa only [d181519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24833 (p : Pattern) (guard : d181520 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181504 p = 1 := by simpa only [d181520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24817 p hg
    simpa only [d181520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24834 (p : Pattern) (guard : d181521 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181474 p = 1 := by simpa only [d181521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24781 p hg
    simpa only [d181521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181520 p = 1 := by simpa only [d181521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24833 p hg
    simpa only [d181521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24835 (p : Pattern) (guard : d181522 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181522, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181522, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181521 p = 1 := by simpa only [d181522, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24834 p hg
    simpa only [d181522, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24836 (p : Pattern) (guard : d181523 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181523, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181523, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181522 p = 1 := by simpa only [d181523, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24835 p hg
    simpa only [d181523, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24837 (p : Pattern) (guard : d181524 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181523 p = 1 := by simpa only [d181524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24836 p hg
    simpa only [d181524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24838 (p : Pattern) (guard : d181525 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181488 p = 1 := by simpa only [d181525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24799 p hg
    simpa only [d181525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181524 p = 1 := by simpa only [d181525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24837 p hg
    simpa only [d181525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24839 (p : Pattern) (guard : d181526 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181525 p = 1 := by simpa only [d181526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24838 p hg
    simpa only [d181526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24840 (p : Pattern) (guard : d181527 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181526 p = 1 := by simpa only [d181527, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24839 p hg
    simpa only [d181527, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181527, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181527, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24841 (p : Pattern) (guard : d181528 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181528, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181528, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181527 p = 1 := by simpa only [d181528, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24840 p hg
    simpa only [d181528, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24842 (p : Pattern) (guard : d181529 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181528 p = 1 := by simpa only [d181529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24841 p hg
    simpa only [d181529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24843 (p : Pattern) (guard : d181530 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181529 p = 1 := by simpa only [d181530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24842 p hg
    simpa only [d181530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24844 (p : Pattern) (guard : d181531 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181530 p = 1 := by simpa only [d181531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24843 p hg
    simpa only [d181531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24845 (p : Pattern) (guard : d181532 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181531 p = 1 := by simpa only [d181532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24844 p hg
    simpa only [d181532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24846 (p : Pattern) (guard : d181533 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181532 p = 1 := by simpa only [d181533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24845 p hg
    simpa only [d181533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24847 (p : Pattern) (guard : d181534 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181533 p = 1 := by simpa only [d181534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24846 p hg
    simpa only [d181534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24848 (p : Pattern) (guard : d181535 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181519 p = 1 := by simpa only [d181535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24832 p hg
    simpa only [d181535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181534 p = 1 := by simpa only [d181535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24847 p hg
    simpa only [d181535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24849 (p : Pattern) (guard : d181536 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181535 p = 1 := by simpa only [d181536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24848 p hg
    simpa only [d181536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24850 (p : Pattern) (guard : d181537 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181536 p = 1 := by simpa only [d181537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24849 p hg
    simpa only [d181537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24851 (p : Pattern) (guard : d181538 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181538, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181538, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181537 p = 1 := by simpa only [d181538, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24850 p hg
    simpa only [d181538, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24852 (p : Pattern) (guard : d181539 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181538 p = 1 := by simpa only [d181539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24851 p hg
    simpa only [d181539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24853 (p : Pattern) (guard : d181540 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181513 p = 1 := by simpa only [d181540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24826 p hg
    simpa only [d181540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24854 (p : Pattern) (guard : d181541 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181540 p = 1 := by simpa only [d181541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24853 p hg
    simpa only [d181541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24855 (p : Pattern) (guard : d181542 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181541 p = 1 := by simpa only [d181542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24854 p hg
    simpa only [d181542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24856 (p : Pattern) (guard : d181543 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181542 p = 1 := by simpa only [d181543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24855 p hg
    simpa only [d181543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24857 (p : Pattern) (guard : d181544 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181543 p = 1 := by simpa only [d181544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24856 p hg
    simpa only [d181544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24858 (p : Pattern) (guard : d181545 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181544 p = 1 := by simpa only [d181545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24857 p hg
    simpa only [d181545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24859 (p : Pattern) (guard : d181546 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181545 p = 1 := by simpa only [d181546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24858 p hg
    simpa only [d181546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24860 (p : Pattern) (guard : d181547 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181546 p = 1 := by simpa only [d181547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24859 p hg
    simpa only [d181547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24861 (p : Pattern) (guard : d181548 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181547 p = 1 := by simpa only [d181548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24860 p hg
    simpa only [d181548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24862 (p : Pattern) (guard : d181549 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181549, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181549, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181548 p = 1 := by simpa only [d181549, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24861 p hg
    simpa only [d181549, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24863 (p : Pattern) (guard : d181550 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181549 p = 1 := by simpa only [d181550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24862 p hg
    simpa only [d181550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24864 (p : Pattern) (guard : d181551 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181539 p = 1 := by simpa only [d181551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24852 p hg
    simpa only [d181551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181550 p = 1 := by simpa only [d181551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24863 p hg
    simpa only [d181551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24865 (p : Pattern) (guard : d181552 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181551 p = 1 := by simpa only [d181552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24864 p hg
    simpa only [d181552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24866 (p : Pattern) (guard : d181553 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181552 p = 1 := by simpa only [d181553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24865 p hg
    simpa only [d181553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24867 (p : Pattern) (guard : d181554 p = 1) : d48748 p ≤ (3 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181553 p = 1 := by simpa only [d181554, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24866 p hg
    simpa only [d181554, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181554, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24155 p hg
    simpa only [d181554, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24868 (p : Pattern) (guard : d181555 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181555, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24114 p hg
    simpa only [d181555, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181554 p = 1 := by simpa only [d181555, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24867 p hg
    simpa only [d181555, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24869 (p : Pattern) (guard : d181556 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181555 p = 1 := by simpa only [d181556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24868 p hg
    simpa only [d181556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24870 (p : Pattern) (guard : d181557 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181556 p = 1 := by simpa only [d181557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24869 p hg
    simpa only [d181557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24871 (p : Pattern) (guard : d181558 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181557 p = 1 := by simpa only [d181558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24870 p hg
    simpa only [d181558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24872 (p : Pattern) (guard : d181559 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181558 p = 1 := by simpa only [d181559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24871 p hg
    simpa only [d181559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24873 (p : Pattern) (guard : d181560 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181559 p = 1 := by simpa only [d181560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24872 p hg
    simpa only [d181560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24874 (p : Pattern) (guard : d181561 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181560 p = 1 := by simpa only [d181561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24873 p hg
    simpa only [d181561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24875 (p : Pattern) (guard : d181562 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181561 p = 1 := by simpa only [d181562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24874 p hg
    simpa only [d181562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24876 (p : Pattern) (guard : d181563 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181562 p = 1 := by simpa only [d181563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24875 p hg
    simpa only [d181563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24877 (p : Pattern) (guard : d181564 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181563 p = 1 := by simpa only [d181564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24876 p hg
    simpa only [d181564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24878 (p : Pattern) (guard : d181565 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181564 p = 1 := by simpa only [d181565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24877 p hg
    simpa only [d181565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24879 (p : Pattern) (guard : d181566 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d181441 p = 1 := by simpa only [d181566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24732 p hg
    simpa only [d181566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181565 p = 1 := by simpa only [d181566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24878 p hg
    simpa only [d181566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24880 (p : Pattern) (guard : d181567 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 260 with
  | false =>
    have hg : d181566 p = 1 := by simpa only [d181567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24879 p hg
    simpa only [d181567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24881 (p : Pattern) (guard : d181568 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 259 with
  | false =>
    have hg : d181567 p = 1 := by simpa only [d181568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24880 p hg
    simpa only [d181568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24882 (p : Pattern) (guard : d181569 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 258 with
  | false =>
    have hg : d181568 p = 1 := by simpa only [d181569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24881 p hg
    simpa only [d181569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24883 (p : Pattern) (guard : d181570 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 257 with
  | false =>
    have hg : d181569 p = 1 := by simpa only [d181570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24882 p hg
    simpa only [d181570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24884 (p : Pattern) (guard : d181571 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 256 with
  | false =>
    have hg : d181570 p = 1 := by simpa only [d181571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24883 p hg
    simpa only [d181571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24885 (p : Pattern) (guard : d181572 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 255 with
  | false =>
    have hg : d181571 p = 1 := by simpa only [d181572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24884 p hg
    simpa only [d181572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24886 (p : Pattern) (guard : d181573 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 254 with
  | false =>
    have hg : d181572 p = 1 := by simpa only [d181573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24885 p hg
    simpa only [d181573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24887 (p : Pattern) (guard : d181574 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 253 with
  | false =>
    have hg : d181573 p = 1 := by simpa only [d181574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24886 p hg
    simpa only [d181574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24888 (p : Pattern) (guard : d181575 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 252 with
  | false =>
    have hg : d181574 p = 1 := by simpa only [d181575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24887 p hg
    simpa only [d181575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24889 (p : Pattern) (guard : d181576 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 251 with
  | false =>
    have hg : d181575 p = 1 := by simpa only [d181576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24888 p hg
    simpa only [d181576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24890 (p : Pattern) (guard : d181577 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 250 with
  | false =>
    have hg : d181576 p = 1 := by simpa only [d181577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24889 p hg
    simpa only [d181577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24891 (p : Pattern) (guard : d181578 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 249 with
  | false =>
    have hg : d181577 p = 1 := by simpa only [d181578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24890 p hg
    simpa only [d181578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24892 (p : Pattern) (guard : d181579 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 245 with
  | false =>
    have hg : d181578 p = 1 := by simpa only [d181579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24891 p hg
    simpa only [d181579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24893 (p : Pattern) (guard : d181580 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 200 with
  | false =>
    have hg : d181579 p = 1 := by simpa only [d181580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24892 p hg
    simpa only [d181580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24894 (p : Pattern) (guard : d181581 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 199 with
  | false =>
    have hg : d181580 p = 1 := by simpa only [d181581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24893 p hg
    simpa only [d181581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24895 (p : Pattern) (guard : d181582 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 186 with
  | false =>
    have hg : d181581 p = 1 := by simpa only [d181582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24894 p hg
    simpa only [d181582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24896 (p : Pattern) (guard : d181583 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 185 with
  | false =>
    have hg : d181582 p = 1 := by simpa only [d181583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24895 p hg
    simpa only [d181583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24897 (p : Pattern) (guard : d181584 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 184 with
  | false =>
    have hg : d181583 p = 1 := by simpa only [d181584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24896 p hg
    simpa only [d181584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24898 (p : Pattern) (guard : d181585 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 181 with
  | false =>
    have hg : d181584 p = 1 := by simpa only [d181585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24897 p hg
    simpa only [d181585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24899 (p : Pattern) (guard : d181586 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 177 with
  | false =>
    have hg : d181585 p = 1 := by simpa only [d181586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24898 p hg
    simpa only [d181586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24900 (p : Pattern) (guard : d181587 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 164 with
  | false =>
    have hg : d181586 p = 1 := by simpa only [d181587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24899 p hg
    simpa only [d181587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24901 (p : Pattern) (guard : d181588 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 156 with
  | false =>
    have hg : d181587 p = 1 := by simpa only [d181588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24900 p hg
    simpa only [d181588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24902 (p : Pattern) (guard : d181589 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 155 with
  | false =>
    have hg : d181588 p = 1 := by simpa only [d181589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24901 p hg
    simpa only [d181589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24903 (p : Pattern) (guard : d181590 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 134 with
  | false =>
    have hg : d181589 p = 1 := by simpa only [d181590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24902 p hg
    simpa only [d181590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24904 (p : Pattern) (guard : d181591 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 133 with
  | false =>
    have hg : d181590 p = 1 := by simpa only [d181591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24903 p hg
    simpa only [d181591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24905 (p : Pattern) (guard : d181592 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 120 with
  | false =>
    have hg : d181591 p = 1 := by simpa only [d181592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24904 p hg
    simpa only [d181592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24906 (p : Pattern) (guard : d181593 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 118 with
  | false =>
    have hg : d181592 p = 1 := by simpa only [d181593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24905 p hg
    simpa only [d181593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24907 (p : Pattern) (guard : d181594 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 114 with
  | false =>
    have hg : d181593 p = 1 := by simpa only [d181594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24906 p hg
    simpa only [d181594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24908 (p : Pattern) (guard : d181595 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 111 with
  | false =>
    have hg : d181594 p = 1 := by simpa only [d181595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24907 p hg
    simpa only [d181595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24909 (p : Pattern) (guard : d181596 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 98 with
  | false =>
    have hg : d181595 p = 1 := by simpa only [d181596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24908 p hg
    simpa only [d181596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24910 (p : Pattern) (guard : d181597 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 97 with
  | false =>
    have hg : d181596 p = 1 := by simpa only [d181597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24909 p hg
    simpa only [d181597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24911 (p : Pattern) (guard : d181598 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 94 with
  | false =>
    have hg : d181597 p = 1 := by simpa only [d181598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24910 p hg
    simpa only [d181598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24912 (p : Pattern) (guard : d181599 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 76 with
  | false =>
    have hg : d181598 p = 1 := by simpa only [d181599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24911 p hg
    simpa only [d181599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24913 (p : Pattern) (guard : d181600 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 67 with
  | false =>
    have hg : d181599 p = 1 := by simpa only [d181600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24912 p hg
    simpa only [d181600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24914 (p : Pattern) (guard : d181601 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 52 with
  | false =>
    have hg : d181600 p = 1 := by simpa only [d181601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24913 p hg
    simpa only [d181601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24915 (p : Pattern) (guard : d181602 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 47 with
  | false =>
    have hg : d181601 p = 1 := by simpa only [d181602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24914 p hg
    simpa only [d181602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24916 (p : Pattern) (guard : d181603 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 46 with
  | false =>
    have hg : d181602 p = 1 := by simpa only [d181603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24915 p hg
    simpa only [d181603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24917 (p : Pattern) (guard : d181604 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 45 with
  | false =>
    have hg : d181603 p = 1 := by simpa only [d181604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24916 p hg
    simpa only [d181604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24918 (p : Pattern) (guard : d181605 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 30 with
  | false =>
    have hg : d181604 p = 1 := by simpa only [d181605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24917 p hg
    simpa only [d181605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24919 (p : Pattern) (guard : d181606 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 29 with
  | false =>
    have hg : d181605 p = 1 := by simpa only [d181606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24918 p hg
    simpa only [d181606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24920 (p : Pattern) (guard : d181607 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 28 with
  | false =>
    have hg : d181606 p = 1 := by simpa only [d181607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24919 p hg
    simpa only [d181607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24921 (p : Pattern) (guard : d181608 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 27 with
  | false =>
    have hg : d181607 p = 1 := by simpa only [d181608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24920 p hg
    simpa only [d181608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24922 (p : Pattern) (guard : d181609 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 25 with
  | false =>
    have hg : d181608 p = 1 := by simpa only [d181609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24921 p hg
    simpa only [d181609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24923 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24924 (p : Pattern) (guard : d0 p = 1) : d48697 p ≤ (2 : Int) + d130446 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24925 (p : Pattern) (guard : d0 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24926 (p : Pattern) (guard : d0 p = 1) : d48613 p ≤ (2 : Int) + d130418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24927 (p : Pattern) (guard : d0 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24928 (p : Pattern) (guard : d0 p = 1) : d48630 p ≤ (2 : Int) + d130415 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24929 (p : Pattern) (guard : d0 p = 1) : d48635 p ≤ (2 : Int) + d130404 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24930 (p : Pattern) (guard : d0 p = 1) : d48602 p ≤ (2 : Int) + d130406 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24931 (p : Pattern) (guard : d66 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare24932 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24933 (p : Pattern) (guard : d18534 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d66 p = 1 := by simpa only [d18534, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24931 p hg
    simpa only [d18534, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18534, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d18534, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24934 (p : Pattern) (guard : d0 p = 1) : d48571 p ≤ (2 : Int) + d130398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24935 (p : Pattern) (guard : d180909 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18534 p = 1 := by simpa only [d180909, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24933 p hg
    simpa only [d180909, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180909, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d180909, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24936 (p : Pattern) (guard : d0 p = 1) : d48700 p ≤ (2 : Int) + d48700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24937 (p : Pattern) (guard : d180910 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180909 p = 1 := by simpa only [d180910, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24935 p hg
    simpa only [d180910, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180910, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d180910, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24938 (p : Pattern) (guard : d0 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24939 (p : Pattern) (guard : d180911 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180910 p = 1 := by simpa only [d180911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24937 p hg
    simpa only [d180911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d180911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24940 (p : Pattern) (guard : d180912 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180911 p = 1 := by simpa only [d180912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24939 p hg
    simpa only [d180912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d180912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24941 (p : Pattern) (guard : d180913 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180912 p = 1 := by simpa only [d180913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24940 p hg
    simpa only [d180913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d180913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24942 (p : Pattern) (guard : d180914 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180914, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d180914, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180913 p = 1 := by simpa only [d180914, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24941 p hg
    simpa only [d180914, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24943 (p : Pattern) (guard : d180915 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180915, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d180915, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180914 p = 1 := by simpa only [d180915, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24942 p hg
    simpa only [d180915, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24944 (p : Pattern) (guard : d0 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24945 (p : Pattern) (guard : d180916 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180915 p = 1 := by simpa only [d180916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24943 p hg
    simpa only [d180916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d180916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24946 (p : Pattern) (guard : d180917 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180916 p = 1 := by simpa only [d180917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24945 p hg
    simpa only [d180917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d180917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24947 (p : Pattern) (guard : d180918 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180917 p = 1 := by simpa only [d180918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24946 p hg
    simpa only [d180918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d180918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24948 (p : Pattern) (guard : d0 p = 1) : d48704 p ≤ (2 : Int) + d130451 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24949 (p : Pattern) (guard : d180919 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180918 p = 1 := by simpa only [d180919, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24947 p hg
    simpa only [d180919, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180919, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d180919, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24950 (p : Pattern) (guard : d180920 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180920, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d180920, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180919 p = 1 := by simpa only [d180920, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24949 p hg
    simpa only [d180920, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24951 (p : Pattern) (guard : d180921 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180920 p = 1 := by simpa only [d180921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24950 p hg
    simpa only [d180921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d180921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24952 (p : Pattern) (guard : d180922 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180921 p = 1 := by simpa only [d180922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24951 p hg
    simpa only [d180922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d180922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24953 (p : Pattern) (guard : d180923 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180922 p = 1 := by simpa only [d180923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24952 p hg
    simpa only [d180923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d180923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24954 (p : Pattern) (guard : d180924 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180923 p = 1 := by simpa only [d180924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24953 p hg
    simpa only [d180924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d180924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24955 (p : Pattern) (guard : d180925 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180924 p = 1 := by simpa only [d180925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24954 p hg
    simpa only [d180925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d180925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24956 (p : Pattern) (guard : d181006 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180925 p = 1 := by simpa only [d181006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24955 p hg
    simpa only [d181006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24957 (p : Pattern) (guard : d181007 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181006 p = 1 := by simpa only [d181007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24956 p hg
    simpa only [d181007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24958 (p : Pattern) (guard : d181008 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181007 p = 1 := by simpa only [d181008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24957 p hg
    simpa only [d181008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24959 (p : Pattern) (guard : d181009 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181008 p = 1 := by simpa only [d181009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24958 p hg
    simpa only [d181009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24960 (p : Pattern) (guard : d181010 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181010, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24926 p hg
    simpa only [d181010, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181009 p = 1 := by simpa only [d181010, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24959 p hg
    simpa only [d181010, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24961 (p : Pattern) (guard : d181011 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181010 p = 1 := by simpa only [d181011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24960 p hg
    simpa only [d181011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24962 (p : Pattern) (guard : d181610 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181011 p = 1 := by simpa only [d181610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24961 p hg
    simpa only [d181610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24963 (p : Pattern) (guard : d181611 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181610 p = 1 := by simpa only [d181611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24962 p hg
    simpa only [d181611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24964 (p : Pattern) (guard : d181612 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181611 p = 1 := by simpa only [d181612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24963 p hg
    simpa only [d181612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24965 (p : Pattern) (guard : d0 p = 1) : d48747 p ≤ (2 : Int) + d130477 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24966 (p : Pattern) (guard : d181613 p = 1) : d48748 p ≤ (2 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181612 p = 1 := by simpa only [d181613, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24964 p hg
    simpa only [d181613, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181613, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24965 p hg
    simpa only [d181613, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24967 (p : Pattern) (guard : d181614 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181614, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24924 p hg
    simpa only [d181614, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181613 p = 1 := by simpa only [d181614, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24966 p hg
    simpa only [d181614, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24968 (p : Pattern) (guard : d181615 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181614 p = 1 := by simpa only [d181615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24967 p hg
    simpa only [d181615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24969 (p : Pattern) (guard : d181616 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181615 p = 1 := by simpa only [d181616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24968 p hg
    simpa only [d181616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24970 (p : Pattern) (guard : d181617 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181616 p = 1 := by simpa only [d181617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24969 p hg
    simpa only [d181617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24971 (p : Pattern) (guard : d181618 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181617 p = 1 := by simpa only [d181618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24970 p hg
    simpa only [d181618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24972 (p : Pattern) (guard : d181619 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181618 p = 1 := by simpa only [d181619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24971 p hg
    simpa only [d181619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24973 (p : Pattern) (guard : d226 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare24974 (p : Pattern) (guard : d18571 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d226 p = 1 := by simpa only [d18571, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24973 p hg
    simpa only [d18571, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18571, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d18571, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24975 (p : Pattern) (guard : d180941 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18571 p = 1 := by simpa only [d180941, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24974 p hg
    simpa only [d180941, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180941, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d180941, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24976 (p : Pattern) (guard : d180942 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180941 p = 1 := by simpa only [d180942, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24975 p hg
    simpa only [d180942, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180942, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d180942, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24977 (p : Pattern) (guard : d180943 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180942 p = 1 := by simpa only [d180943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24976 p hg
    simpa only [d180943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180910 p = 1 := by simpa only [d180943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24937 p hg
    simpa only [d180943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24978 (p : Pattern) (guard : d180944 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180943 p = 1 := by simpa only [d180944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24977 p hg
    simpa only [d180944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180911 p = 1 := by simpa only [d180944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24939 p hg
    simpa only [d180944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24979 (p : Pattern) (guard : d180945 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180944 p = 1 := by simpa only [d180945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24978 p hg
    simpa only [d180945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180912 p = 1 := by simpa only [d180945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24940 p hg
    simpa only [d180945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24980 (p : Pattern) (guard : d180946 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180946, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d180946, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180945 p = 1 := by simpa only [d180946, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24979 p hg
    simpa only [d180946, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24981 (p : Pattern) (guard : d180947 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180947, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d180947, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180946 p = 1 := by simpa only [d180947, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24980 p hg
    simpa only [d180947, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24982 (p : Pattern) (guard : d180948 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180947 p = 1 := by simpa only [d180948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24981 p hg
    simpa only [d180948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180915 p = 1 := by simpa only [d180948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24943 p hg
    simpa only [d180948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24983 (p : Pattern) (guard : d180949 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180948 p = 1 := by simpa only [d180949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24982 p hg
    simpa only [d180949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180916 p = 1 := by simpa only [d180949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24945 p hg
    simpa only [d180949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24984 (p : Pattern) (guard : d180950 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180949 p = 1 := by simpa only [d180950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24983 p hg
    simpa only [d180950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d180950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24985 (p : Pattern) (guard : d180951 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180950 p = 1 := by simpa only [d180951, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24984 p hg
    simpa only [d180951, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180951, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d180951, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24986 (p : Pattern) (guard : d180952 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180952, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d180952, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180951 p = 1 := by simpa only [d180952, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24985 p hg
    simpa only [d180952, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24987 (p : Pattern) (guard : d180953 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180952 p = 1 := by simpa only [d180953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24986 p hg
    simpa only [d180953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180920 p = 1 := by simpa only [d180953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24950 p hg
    simpa only [d180953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24988 (p : Pattern) (guard : d180954 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180953 p = 1 := by simpa only [d180954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24987 p hg
    simpa only [d180954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d180954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24989 (p : Pattern) (guard : d180955 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180954 p = 1 := by simpa only [d180955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24988 p hg
    simpa only [d180955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d180955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24990 (p : Pattern) (guard : d180956 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180955 p = 1 := by simpa only [d180956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24989 p hg
    simpa only [d180956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d180956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24991 (p : Pattern) (guard : d180957 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180956 p = 1 := by simpa only [d180957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24990 p hg
    simpa only [d180957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180924 p = 1 := by simpa only [d180957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24954 p hg
    simpa only [d180957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24992 (p : Pattern) (guard : d181620 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180957 p = 1 := by simpa only [d181620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24991 p hg
    simpa only [d181620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24993 (p : Pattern) (guard : d181621 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181620 p = 1 := by simpa only [d181621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24992 p hg
    simpa only [d181621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24994 (p : Pattern) (guard : d181622 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181621 p = 1 := by simpa only [d181622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24993 p hg
    simpa only [d181622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24995 (p : Pattern) (guard : d181623 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181622 p = 1 := by simpa only [d181623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24994 p hg
    simpa only [d181623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24996 (p : Pattern) (guard : d181624 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181624, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24926 p hg
    simpa only [d181624, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181623 p = 1 := by simpa only [d181624, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24995 p hg
    simpa only [d181624, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24997 (p : Pattern) (guard : d181625 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181624 p = 1 := by simpa only [d181625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24996 p hg
    simpa only [d181625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24998 (p : Pattern) (guard : d181626 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181625 p = 1 := by simpa only [d181626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24997 p hg
    simpa only [d181626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24999 (p : Pattern) (guard : d181627 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181626 p = 1 := by simpa only [d181627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24998 p hg
    simpa only [d181627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181627, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
