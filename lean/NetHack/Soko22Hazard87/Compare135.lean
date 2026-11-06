import NetHack.Soko22Hazard87.Compare134
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33750 (p : Pattern) (guard : d295443 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295443, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295443, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295442 p = 1 := by simpa only [d295443, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33749 p hg
    simpa only [d295443, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33751 (p : Pattern) (guard : d295444 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295443 p = 1 := by simpa only [d295444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33750 p hg
    simpa only [d295444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33752 (p : Pattern) (guard : d295445 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295418 p = 1 := by simpa only [d295445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33725 p hg
    simpa only [d295445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33753 (p : Pattern) (guard : d295446 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295445 p = 1 := by simpa only [d295446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33752 p hg
    simpa only [d295446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33754 (p : Pattern) (guard : d295447 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295446 p = 1 := by simpa only [d295447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33753 p hg
    simpa only [d295447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33755 (p : Pattern) (guard : d295448 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295447 p = 1 := by simpa only [d295448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33754 p hg
    simpa only [d295448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33756 (p : Pattern) (guard : d295449 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295448 p = 1 := by simpa only [d295449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33755 p hg
    simpa only [d295449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33757 (p : Pattern) (guard : d295450 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295449 p = 1 := by simpa only [d295450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33756 p hg
    simpa only [d295450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33758 (p : Pattern) (guard : d295451 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295450 p = 1 := by simpa only [d295451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33757 p hg
    simpa only [d295451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33759 (p : Pattern) (guard : d295452 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295451 p = 1 := by simpa only [d295452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33758 p hg
    simpa only [d295452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33760 (p : Pattern) (guard : d295453 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295452 p = 1 := by simpa only [d295453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33759 p hg
    simpa only [d295453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33761 (p : Pattern) (guard : d295454 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295454, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295454, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295453 p = 1 := by simpa only [d295454, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33760 p hg
    simpa only [d295454, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33762 (p : Pattern) (guard : d295455 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295454 p = 1 := by simpa only [d295455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33761 p hg
    simpa only [d295455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33763 (p : Pattern) (guard : d295456 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295444 p = 1 := by simpa only [d295456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33751 p hg
    simpa only [d295456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295455 p = 1 := by simpa only [d295456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33762 p hg
    simpa only [d295456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33764 (p : Pattern) (guard : d295457 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295456 p = 1 := by simpa only [d295457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33763 p hg
    simpa only [d295457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33765 (p : Pattern) (guard : d295458 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295457 p = 1 := by simpa only [d295458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33764 p hg
    simpa only [d295458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33766 (p : Pattern) (guard : d295459 p = 1) : d50100 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295458 p = 1 := by simpa only [d295459, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33765 p hg
    simpa only [d295459, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295459, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32160 p hg
    simpa only [d295459, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33767 (p : Pattern) (guard : d295460 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d295386 p = 1 := by simpa only [d295460, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33669 p hg
    simpa only [d295460, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295459 p = 1 := by simpa only [d295460, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33766 p hg
    simpa only [d295460, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33768 (p : Pattern) (guard : d295461 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295460 p = 1 := by simpa only [d295461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33767 p hg
    simpa only [d295461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33769 (p : Pattern) (guard : d295462 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295461 p = 1 := by simpa only [d295462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33768 p hg
    simpa only [d295462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33770 (p : Pattern) (guard : d295463 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295462 p = 1 := by simpa only [d295463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33769 p hg
    simpa only [d295463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33771 (p : Pattern) (guard : d295464 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295463 p = 1 := by simpa only [d295464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33770 p hg
    simpa only [d295464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33772 (p : Pattern) (guard : d295465 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295464 p = 1 := by simpa only [d295465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33771 p hg
    simpa only [d295465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33773 (p : Pattern) (guard : d295466 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295465 p = 1 := by simpa only [d295466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33772 p hg
    simpa only [d295466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33774 (p : Pattern) (guard : d295467 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295466 p = 1 := by simpa only [d295467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33773 p hg
    simpa only [d295467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33775 (p : Pattern) (guard : d295468 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295467 p = 1 := by simpa only [d295468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33774 p hg
    simpa only [d295468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33776 (p : Pattern) (guard : d295469 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295468 p = 1 := by simpa only [d295469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33775 p hg
    simpa only [d295469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33777 (p : Pattern) (guard : d295470 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295469 p = 1 := by simpa only [d295470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33776 p hg
    simpa only [d295470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33778 (p : Pattern) (guard : d295471 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d295241 p = 1 := by simpa only [d295471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33361 p hg
    simpa only [d295471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295470 p = 1 := by simpa only [d295471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33777 p hg
    simpa only [d295471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33779 (p : Pattern) (guard : d295472 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d295471 p = 1 := by simpa only [d295472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33778 p hg
    simpa only [d295472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33780 (p : Pattern) (guard : d295473 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d295472 p = 1 := by simpa only [d295473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33779 p hg
    simpa only [d295473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33781 (p : Pattern) (guard : d295474 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d295473 p = 1 := by simpa only [d295474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33780 p hg
    simpa only [d295474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33782 (p : Pattern) (guard : d295475 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d295474 p = 1 := by simpa only [d295475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33781 p hg
    simpa only [d295475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33783 (p : Pattern) (guard : d295476 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d295475 p = 1 := by simpa only [d295476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33782 p hg
    simpa only [d295476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33784 (p : Pattern) (guard : d295477 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d295476 p = 1 := by simpa only [d295477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33783 p hg
    simpa only [d295477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33785 (p : Pattern) (guard : d295478 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d295477 p = 1 := by simpa only [d295478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33784 p hg
    simpa only [d295478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33786 (p : Pattern) (guard : d295479 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d295478 p = 1 := by simpa only [d295479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33785 p hg
    simpa only [d295479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33787 (p : Pattern) (guard : d295480 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d295479 p = 1 := by simpa only [d295480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33786 p hg
    simpa only [d295480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33788 (p : Pattern) (guard : d295481 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d295480 p = 1 := by simpa only [d295481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33787 p hg
    simpa only [d295481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33789 (p : Pattern) (guard : d295482 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d295481 p = 1 := by simpa only [d295482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33788 p hg
    simpa only [d295482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33790 (p : Pattern) (guard : d295483 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d295482 p = 1 := by simpa only [d295483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33789 p hg
    simpa only [d295483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33791 (p : Pattern) (guard : d295484 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d295483 p = 1 := by simpa only [d295484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33790 p hg
    simpa only [d295484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33792 (p : Pattern) (guard : d295485 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d295484 p = 1 := by simpa only [d295485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33791 p hg
    simpa only [d295485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33793 (p : Pattern) (guard : d295486 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d295485 p = 1 := by simpa only [d295486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33792 p hg
    simpa only [d295486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33794 (p : Pattern) (guard : d295487 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d295486 p = 1 := by simpa only [d295487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33793 p hg
    simpa only [d295487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33795 (p : Pattern) (guard : d295488 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d295487 p = 1 := by simpa only [d295488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33794 p hg
    simpa only [d295488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33796 (p : Pattern) (guard : d295489 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d295488 p = 1 := by simpa only [d295489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33795 p hg
    simpa only [d295489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33797 (p : Pattern) (guard : d295490 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d295489 p = 1 := by simpa only [d295490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33796 p hg
    simpa only [d295490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33798 (p : Pattern) (guard : d295491 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d295490 p = 1 := by simpa only [d295491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33797 p hg
    simpa only [d295491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33799 (p : Pattern) (guard : d295492 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d295491 p = 1 := by simpa only [d295492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33798 p hg
    simpa only [d295492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33800 (p : Pattern) (guard : d295493 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d295492 p = 1 := by simpa only [d295493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33799 p hg
    simpa only [d295493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33801 (p : Pattern) (guard : d295494 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d295493 p = 1 := by simpa only [d295494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33800 p hg
    simpa only [d295494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33802 (p : Pattern) (guard : d295495 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d295494 p = 1 := by simpa only [d295495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33801 p hg
    simpa only [d295495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33803 (p : Pattern) (guard : d295496 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d295495 p = 1 := by simpa only [d295496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33802 p hg
    simpa only [d295496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33804 (p : Pattern) (guard : d295497 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d295496 p = 1 := by simpa only [d295497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33803 p hg
    simpa only [d295497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33805 (p : Pattern) (guard : d295498 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d295497 p = 1 := by simpa only [d295498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33804 p hg
    simpa only [d295498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33806 (p : Pattern) (guard : d295499 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d295498 p = 1 := by simpa only [d295499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33805 p hg
    simpa only [d295499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33807 (p : Pattern) (guard : d295500 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d295499 p = 1 := by simpa only [d295500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33806 p hg
    simpa only [d295500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33808 (p : Pattern) (guard : d295501 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d295500 p = 1 := by simpa only [d295501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33807 p hg
    simpa only [d295501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33809 (p : Pattern) (guard : d295502 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d295501 p = 1 := by simpa only [d295502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33808 p hg
    simpa only [d295502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33810 (p : Pattern) (guard : d295503 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d295502 p = 1 := by simpa only [d295503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33809 p hg
    simpa only [d295503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33811 (p : Pattern) (guard : d295504 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d295503 p = 1 := by simpa only [d295504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33810 p hg
    simpa only [d295504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33812 (p : Pattern) (guard : d295505 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d295504 p = 1 := by simpa only [d295505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33811 p hg
    simpa only [d295505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33813 (p : Pattern) (guard : d295506 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d295505 p = 1 := by simpa only [d295506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33812 p hg
    simpa only [d295506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33814 (p : Pattern) (guard : d295507 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d295506 p = 1 := by simpa only [d295507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33813 p hg
    simpa only [d295507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33815 (p : Pattern) (guard : d295508 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d295507 p = 1 := by simpa only [d295508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33814 p hg
    simpa only [d295508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33816 (p : Pattern) (guard : d295509 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d295508 p = 1 := by simpa only [d295509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33815 p hg
    simpa only [d295509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33817 (p : Pattern) (guard : d295510 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d295509 p = 1 := by simpa only [d295510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33816 p hg
    simpa only [d295510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33818 (p : Pattern) (guard : d295511 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d295510 p = 1 := by simpa only [d295511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33817 p hg
    simpa only [d295511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33819 (p : Pattern) (guard : d295512 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d295511 p = 1 := by simpa only [d295512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33818 p hg
    simpa only [d295512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33820 (p : Pattern) (guard : d295513 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d295512 p = 1 := by simpa only [d295513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33819 p hg
    simpa only [d295513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33821 (p : Pattern) (guard : d295514 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d295513 p = 1 := by simpa only [d295514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33820 p hg
    simpa only [d295514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33822 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33823 (p : Pattern) (guard : d0 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33824 (p : Pattern) (guard : d0 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33825 (p : Pattern) (guard : d0 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33826 (p : Pattern) (guard : d0 p = 1) : d49910 p ≤ (0 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33827 (p : Pattern) (guard : d0 p = 1) : d49912 p ≤ (0 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33828 (p : Pattern) (guard : d0 p = 1) : d49861 p ≤ (0 : Int) + d47681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33829 (p : Pattern) (guard : d0 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33830 (p : Pattern) (guard : d0 p = 1) : d49863 p ≤ (0 : Int) + d47655 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33831 (p : Pattern) (guard : d0 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33832 (p : Pattern) (guard : d17 p = 1) : d47617 p ≤ (0 : Int) + d47617 p := by
  omega
theorem compare33833 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33834 (p : Pattern) (guard : d18 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33832 p hg
    simpa only [d18, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33833 p hg
    simpa only [d18, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33835 (p : Pattern) (guard : d19 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33834 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33836 (p : Pattern) (guard : d20 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33835 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33837 (p : Pattern) (guard : d29090 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33836 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33838 (p : Pattern) (guard : d294503 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29090 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33837 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33839 (p : Pattern) (guard : d0 p = 1) : d49796 p ≤ (0 : Int) + d47618 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33840 (p : Pattern) (guard : d294504 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294503 p = 1 := by simpa only [d294504, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33838 p hg
    simpa only [d294504, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294504, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33839 p hg
    simpa only [d294504, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33841 (p : Pattern) (guard : d0 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33842 (p : Pattern) (guard : d294505 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294504 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33840 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33841 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33843 (p : Pattern) (guard : d0 p = 1) : d49837 p ≤ (0 : Int) + d47659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33844 (p : Pattern) (guard : d294506 p = 1) : d49838 p ≤ (0 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294505 p = 1 := by simpa only [d294506, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33842 p hg
    simpa only [d294506, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294506, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33843 p hg
    simpa only [d294506, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33845 (p : Pattern) (guard : d0 p = 1) : d49840 p ≤ (0 : Int) + d47662 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33846 (p : Pattern) (guard : d294507 p = 1) : d49841 p ≤ (0 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294506 p = 1 := by simpa only [d294507, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33844 p hg
    simpa only [d294507, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294507, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33845 p hg
    simpa only [d294507, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33847 (p : Pattern) (guard : d294508 p = 1) : d49864 p ≤ (0 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294508, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33830 p hg
    simpa only [d294508, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294507 p = 1 := by simpa only [d294508, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33846 p hg
    simpa only [d294508, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33848 (p : Pattern) (guard : d0 p = 1) : d49867 p ≤ (0 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33849 (p : Pattern) (guard : d294509 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294508 p = 1 := by simpa only [d294509, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33847 p hg
    simpa only [d294509, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294509, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33848 p hg
    simpa only [d294509, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33850 (p : Pattern) (guard : d294510 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294509 p = 1 := by simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33849 p hg
    simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33851 (p : Pattern) (guard : d205892 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d29090 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33837 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33852 (p : Pattern) (guard : d205893 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d205892 p = 1 := by simpa only [d205893, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33851 p hg
    simpa only [d205893, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205893, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33839 p hg
    simpa only [d205893, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33853 (p : Pattern) (guard : d205894 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d205893 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33852 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33841 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33854 (p : Pattern) (guard : d205895 p = 1) : d49838 p ≤ (0 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d205894 p = 1 := by simpa only [d205895, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33853 p hg
    simpa only [d205895, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205895, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33843 p hg
    simpa only [d205895, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33855 (p : Pattern) (guard : d205896 p = 1) : d49841 p ≤ (0 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d205895 p = 1 := by simpa only [d205896, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33854 p hg
    simpa only [d205896, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205896, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33845 p hg
    simpa only [d205896, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33856 (p : Pattern) (guard : d205897 p = 1) : d49864 p ≤ (0 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205897, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33830 p hg
    simpa only [d205897, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205896 p = 1 := by simpa only [d205897, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33855 p hg
    simpa only [d205897, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33857 (p : Pattern) (guard : d205898 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d205897 p = 1 := by simpa only [d205898, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33856 p hg
    simpa only [d205898, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205898, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33848 p hg
    simpa only [d205898, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33858 (p : Pattern) (guard : d294584 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205898 p = 1 := by simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33857 p hg
    simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33859 (p : Pattern) (guard : d294585 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294510 p = 1 := by simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33850 p hg
    simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294584 p = 1 := by simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33858 p hg
    simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33860 (p : Pattern) (guard : d205899 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d205898 p = 1 := by simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33857 p hg
    simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33861 (p : Pattern) (guard : d294586 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294584 p = 1 := by simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33858 p hg
    simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205899 p = 1 := by simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33860 p hg
    simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33862 (p : Pattern) (guard : d294587 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294585 p = 1 := by simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33859 p hg
    simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294586 p = 1 := by simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33861 p hg
    simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33863 (p : Pattern) (guard : d294588 p = 1) : d49869 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294588, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33828 p hg
    simpa only [d294588, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294587 p = 1 := by simpa only [d294588, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33862 p hg
    simpa only [d294588, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33864 (p : Pattern) (guard : d294589 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294589, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d294589, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294588 p = 1 := by simpa only [d294589, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33863 p hg
    simpa only [d294589, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33865 (p : Pattern) (guard : d205900 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d205899 p = 1 := by simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33860 p hg
    simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33866 (p : Pattern) (guard : d294590 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294586 p = 1 := by simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33861 p hg
    simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205900 p = 1 := by simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33865 p hg
    simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33867 (p : Pattern) (guard : d294591 p = 1) : d49869 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294591, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33828 p hg
    simpa only [d294591, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294590 p = 1 := by simpa only [d294591, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33866 p hg
    simpa only [d294591, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33868 (p : Pattern) (guard : d294592 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294592, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d294592, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294591 p = 1 := by simpa only [d294592, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33867 p hg
    simpa only [d294592, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33869 (p : Pattern) (guard : d294593 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294589 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33864 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294592 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33868 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33870 (p : Pattern) (guard : d0 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33871 (p : Pattern) (guard : d294594 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294592 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33868 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33872 (p : Pattern) (guard : d294595 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294593 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33869 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294594 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33871 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33873 (p : Pattern) (guard : d294596 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294595 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33872 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33874 (p : Pattern) (guard : d0 p = 1) : d49893 p ≤ (0 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33875 (p : Pattern) (guard : d294597 p = 1) : d49914 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294596 p = 1 := by simpa only [d294597, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33873 p hg
    simpa only [d294597, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294597, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d294597, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33876 (p : Pattern) (guard : d294598 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294598, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d294598, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294597 p = 1 := by simpa only [d294598, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33875 p hg
    simpa only [d294598, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33877 (p : Pattern) (guard : d294599 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294594 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33871 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33878 (p : Pattern) (guard : d294600 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294599 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33877 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33879 (p : Pattern) (guard : d294601 p = 1) : d49914 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294600 p = 1 := by simpa only [d294601, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33878 p hg
    simpa only [d294601, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294601, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d294601, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33880 (p : Pattern) (guard : d294602 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294602, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d294602, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294601 p = 1 := by simpa only [d294602, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33879 p hg
    simpa only [d294602, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33881 (p : Pattern) (guard : d294603 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294598 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33876 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294602 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33880 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33882 (p : Pattern) (guard : d294604 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294603 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33881 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33883 (p : Pattern) (guard : d294605 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294604 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33882 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33884 (p : Pattern) (guard : d294606 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294605 p = 1 := by simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33883 p hg
    simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33885 (p : Pattern) (guard : d294607 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294602 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33880 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33886 (p : Pattern) (guard : d294608 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294607 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33885 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33887 (p : Pattern) (guard : d294609 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294608 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33886 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33888 (p : Pattern) (guard : d294610 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294609 p = 1 := by simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33887 p hg
    simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33889 (p : Pattern) (guard : d294611 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294606 p = 1 := by simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33884 p hg
    simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294610 p = 1 := by simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33888 p hg
    simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33890 (p : Pattern) (guard : d294612 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294611 p = 1 := by simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33889 p hg
    simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33891 (p : Pattern) (guard : d294613 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294612 p = 1 := by simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33890 p hg
    simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33892 (p : Pattern) (guard : d294614 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294613 p = 1 := by simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33891 p hg
    simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33893 (p : Pattern) (guard : d294615 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294614 p = 1 := by simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33892 p hg
    simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33894 (p : Pattern) (guard : d294616 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294616, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294616, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294615 p = 1 := by simpa only [d294616, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33893 p hg
    simpa only [d294616, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33895 (p : Pattern) (guard : d0 p = 1) : d49885 p ≤ (0 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33896 (p : Pattern) (guard : d0 p = 1) : d49891 p ≤ (0 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33897 (p : Pattern) (guard : d294589 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294589, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d294589, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294588 p = 1 := by simpa only [d294589, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33863 p hg
    simpa only [d294589, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33898 (p : Pattern) (guard : d294592 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294592, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d294592, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294591 p = 1 := by simpa only [d294592, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33867 p hg
    simpa only [d294592, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33899 (p : Pattern) (guard : d294593 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294589 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33897 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294592 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33898 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33900 (p : Pattern) (guard : d0 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33901 (p : Pattern) (guard : d294594 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294592 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33898 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33902 (p : Pattern) (guard : d294595 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294593 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33899 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294594 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33901 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33903 (p : Pattern) (guard : d294596 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294595 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33902 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33904 (p : Pattern) (guard : d294597 p = 1) : d49894 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294596 p = 1 := by simpa only [d294597, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33903 p hg
    simpa only [d294597, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294597, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d294597, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33905 (p : Pattern) (guard : d294598 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294598, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d294598, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294597 p = 1 := by simpa only [d294598, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33904 p hg
    simpa only [d294598, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33906 (p : Pattern) (guard : d294599 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294594 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33901 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33907 (p : Pattern) (guard : d294600 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294599 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33906 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33908 (p : Pattern) (guard : d294601 p = 1) : d49894 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294600 p = 1 := by simpa only [d294601, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33907 p hg
    simpa only [d294601, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294601, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d294601, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33909 (p : Pattern) (guard : d294602 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294602, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d294602, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294601 p = 1 := by simpa only [d294602, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33908 p hg
    simpa only [d294602, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33910 (p : Pattern) (guard : d294603 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294598 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33905 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294602 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33909 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33911 (p : Pattern) (guard : d294604 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294603 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33910 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33912 (p : Pattern) (guard : d294605 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294604 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33911 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33913 (p : Pattern) (guard : d294606 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294605 p = 1 := by simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33912 p hg
    simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33914 (p : Pattern) (guard : d294607 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294602 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33909 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33915 (p : Pattern) (guard : d294608 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294607 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33914 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33916 (p : Pattern) (guard : d294609 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294608 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33915 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33917 (p : Pattern) (guard : d294610 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294609 p = 1 := by simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33916 p hg
    simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33918 (p : Pattern) (guard : d294611 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294606 p = 1 := by simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33913 p hg
    simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294610 p = 1 := by simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33917 p hg
    simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33919 (p : Pattern) (guard : d294612 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294611 p = 1 := by simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33918 p hg
    simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33920 (p : Pattern) (guard : d294613 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294612 p = 1 := by simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33919 p hg
    simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33921 (p : Pattern) (guard : d294614 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294613 p = 1 := by simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33920 p hg
    simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33922 (p : Pattern) (guard : d294615 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294614 p = 1 := by simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33921 p hg
    simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33923 (p : Pattern) (guard : d294619 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294605 p = 1 := by simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33883 p hg
    simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33924 (p : Pattern) (guard : d294620 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294609 p = 1 := by simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33887 p hg
    simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33925 (p : Pattern) (guard : d294621 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294619 p = 1 := by simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33923 p hg
    simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294620 p = 1 := by simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33924 p hg
    simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33926 (p : Pattern) (guard : d294622 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294621 p = 1 := by simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33925 p hg
    simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33927 (p : Pattern) (guard : d294623 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294622 p = 1 := by simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33926 p hg
    simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33928 (p : Pattern) (guard : d294624 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294623 p = 1 := by simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33927 p hg
    simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33929 (p : Pattern) (guard : d294625 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294624 p = 1 := by simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33928 p hg
    simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33930 (p : Pattern) (guard : d294626 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294615 p = 1 := by simpa only [d294626, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33922 p hg
    simpa only [d294626, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294625 p = 1 := by simpa only [d294626, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33929 p hg
    simpa only [d294626, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33931 (p : Pattern) (guard : d294627 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d294616 p = 1 := by simpa only [d294627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33894 p hg
    simpa only [d294627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294626 p = 1 := by simpa only [d294627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33930 p hg
    simpa only [d294627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33932 (p : Pattern) (guard : d294628 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294627 p = 1 := by simpa only [d294628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33931 p hg
    simpa only [d294628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d294628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33933 (p : Pattern) (guard : d295676 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294628 p = 1 := by simpa only [d295676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33932 p hg
    simpa only [d295676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33934 (p : Pattern) (guard : d295677 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295676 p = 1 := by simpa only [d295677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33933 p hg
    simpa only [d295677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33935 (p : Pattern) (guard : d0 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33936 (p : Pattern) (guard : d0 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33937 (p : Pattern) (guard : d0 p = 1) : d49990 p ≤ (0 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33938 (p : Pattern) (guard : d0 p = 1) : d49996 p ≤ (0 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33939 (p : Pattern) (guard : d0 p = 1) : d49975 p ≤ (0 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33940 (p : Pattern) (guard : d0 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33941 (p : Pattern) (guard : d0 p = 1) : d49977 p ≤ (0 : Int) + d47734 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33942 (p : Pattern) (guard : d0 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33943 (p : Pattern) (guard : d17 p = 1) : d47706 p ≤ (0 : Int) + d47706 p := by
  omega
theorem compare33944 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33945 (p : Pattern) (guard : d18 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33943 p hg
    simpa only [d18, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33944 p hg
    simpa only [d18, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33946 (p : Pattern) (guard : d19 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33945 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33947 (p : Pattern) (guard : d20 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33946 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33948 (p : Pattern) (guard : d29090 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33947 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33949 (p : Pattern) (guard : d294503 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29090 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33948 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33950 (p : Pattern) (guard : d0 p = 1) : d49928 p ≤ (0 : Int) + d47707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33951 (p : Pattern) (guard : d294504 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294503 p = 1 := by simpa only [d294504, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33949 p hg
    simpa only [d294504, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294504, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33950 p hg
    simpa only [d294504, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33952 (p : Pattern) (guard : d0 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33953 (p : Pattern) (guard : d294505 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294504 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33951 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33952 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33954 (p : Pattern) (guard : d0 p = 1) : d49839 p ≤ (0 : Int) + d47661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33955 (p : Pattern) (guard : d294506 p = 1) : d49957 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294505 p = 1 := by simpa only [d294506, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33953 p hg
    simpa only [d294506, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294506, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d294506, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33956 (p : Pattern) (guard : d294507 p = 1) : d49958 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294506 p = 1 := by simpa only [d294507, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33955 p hg
    simpa only [d294507, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294507, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294507, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33957 (p : Pattern) (guard : d294508 p = 1) : d49978 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294508, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33941 p hg
    simpa only [d294508, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294507 p = 1 := by simpa only [d294508, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33956 p hg
    simpa only [d294508, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33958 (p : Pattern) (guard : d0 p = 1) : d49981 p ≤ (0 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33959 (p : Pattern) (guard : d294509 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294508 p = 1 := by simpa only [d294509, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33957 p hg
    simpa only [d294509, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294509, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33958 p hg
    simpa only [d294509, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33960 (p : Pattern) (guard : d294510 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294509 p = 1 := by simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33959 p hg
    simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33961 (p : Pattern) (guard : d205892 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d29090 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33948 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33962 (p : Pattern) (guard : d205893 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d205892 p = 1 := by simpa only [d205893, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33961 p hg
    simpa only [d205893, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205893, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33950 p hg
    simpa only [d205893, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33963 (p : Pattern) (guard : d205894 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d205893 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33962 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33952 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33964 (p : Pattern) (guard : d205895 p = 1) : d49957 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d205894 p = 1 := by simpa only [d205895, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33963 p hg
    simpa only [d205895, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205895, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d205895, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33965 (p : Pattern) (guard : d205896 p = 1) : d49958 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d205895 p = 1 := by simpa only [d205896, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33964 p hg
    simpa only [d205896, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205896, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d205896, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33966 (p : Pattern) (guard : d205897 p = 1) : d49978 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205897, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33941 p hg
    simpa only [d205897, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205896 p = 1 := by simpa only [d205897, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33965 p hg
    simpa only [d205897, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33967 (p : Pattern) (guard : d205898 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d205897 p = 1 := by simpa only [d205898, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33966 p hg
    simpa only [d205898, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205898, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33958 p hg
    simpa only [d205898, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33968 (p : Pattern) (guard : d294584 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205898 p = 1 := by simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33967 p hg
    simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33969 (p : Pattern) (guard : d294585 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294510 p = 1 := by simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33960 p hg
    simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294584 p = 1 := by simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33968 p hg
    simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33970 (p : Pattern) (guard : d205899 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d205898 p = 1 := by simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33967 p hg
    simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33971 (p : Pattern) (guard : d294586 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294584 p = 1 := by simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33968 p hg
    simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205899 p = 1 := by simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33970 p hg
    simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33972 (p : Pattern) (guard : d294587 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294585 p = 1 := by simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33969 p hg
    simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294586 p = 1 := by simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33971 p hg
    simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33973 (p : Pattern) (guard : d294588 p = 1) : d49983 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294588, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d294588, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294587 p = 1 := by simpa only [d294588, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33972 p hg
    simpa only [d294588, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33974 (p : Pattern) (guard : d294589 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294589, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d294589, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294588 p = 1 := by simpa only [d294589, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33973 p hg
    simpa only [d294589, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33975 (p : Pattern) (guard : d205900 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d205899 p = 1 := by simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33970 p hg
    simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33976 (p : Pattern) (guard : d294590 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294586 p = 1 := by simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33971 p hg
    simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205900 p = 1 := by simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33975 p hg
    simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33977 (p : Pattern) (guard : d294591 p = 1) : d49983 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294591, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d294591, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294590 p = 1 := by simpa only [d294591, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33976 p hg
    simpa only [d294591, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33978 (p : Pattern) (guard : d294592 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294592, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d294592, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294591 p = 1 := by simpa only [d294592, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33977 p hg
    simpa only [d294592, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33979 (p : Pattern) (guard : d294593 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294589 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33974 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294592 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33978 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33980 (p : Pattern) (guard : d0 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33981 (p : Pattern) (guard : d294594 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294592 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33978 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33982 (p : Pattern) (guard : d294595 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294593 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33979 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294594 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33981 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33983 (p : Pattern) (guard : d294596 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294595 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33982 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33984 (p : Pattern) (guard : d0 p = 1) : d49998 p ≤ (0 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33985 (p : Pattern) (guard : d294597 p = 1) : d49999 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294596 p = 1 := by simpa only [d294597, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33983 p hg
    simpa only [d294597, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294597, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33984 p hg
    simpa only [d294597, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33986 (p : Pattern) (guard : d294598 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294598, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d294598, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294597 p = 1 := by simpa only [d294598, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33985 p hg
    simpa only [d294598, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33987 (p : Pattern) (guard : d294599 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294594 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33981 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33988 (p : Pattern) (guard : d294600 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294599 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33987 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33989 (p : Pattern) (guard : d294601 p = 1) : d49999 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294600 p = 1 := by simpa only [d294601, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33988 p hg
    simpa only [d294601, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294601, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33984 p hg
    simpa only [d294601, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33990 (p : Pattern) (guard : d294602 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294602, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d294602, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294601 p = 1 := by simpa only [d294602, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33989 p hg
    simpa only [d294602, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33991 (p : Pattern) (guard : d294603 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294598 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33986 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294602 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33990 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33992 (p : Pattern) (guard : d294604 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294603 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33991 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33993 (p : Pattern) (guard : d294605 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294604 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33992 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33994 (p : Pattern) (guard : d294619 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294605 p = 1 := by simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33993 p hg
    simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33995 (p : Pattern) (guard : d294607 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294602 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33990 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33996 (p : Pattern) (guard : d294608 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294607 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33995 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33997 (p : Pattern) (guard : d294609 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294608 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33996 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33998 (p : Pattern) (guard : d294620 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294609 p = 1 := by simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33997 p hg
    simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33999 (p : Pattern) (guard : d294621 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294619 p = 1 := by simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33994 p hg
    simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294620 p = 1 := by simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33998 p hg
    simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
