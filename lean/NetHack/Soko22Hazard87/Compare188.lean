import NetHack.Soko22Hazard87.Compare187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47000 (p : Pattern) (guard : d44996 p = 1) : d47634 p ≤ (1 : Int) + d47634 p := by
  omega
theorem compare47001 (p : Pattern) (guard : d14 p = 1) : d6 p ≤ (1 : Int) + d47633 p := by
  have ha := bounds6 p
  have hb := bounds47633 p
  omega
theorem compare47002 (p : Pattern) (guard : d0 p = 1) : d47633 p ≤ (1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47003 (p : Pattern) (guard : d15 p = 1) : d47634 p ≤ (1 : Int) + d47963 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47634, d47963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47001 p hg
    simpa only [d15, d47634, d47963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47634, d47963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47002 p hg
    simpa only [d15, d47634, d47963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47004 (p : Pattern) (guard : d45587 p = 1) : d47634 p ≤ (1 : Int) + d47963 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46782 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47003 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47005 (p : Pattern) (guard : d45588 p = 1) : d47634 p ≤ (1 : Int) + d49319 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d45588, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47000 p hg
    simpa only [d45588, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d45588, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47004 p hg
    simpa only [d45588, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47006 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (1 : Int) + d49321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47007 (p : Pattern) (guard : d14 p = 1) : d6 p ≤ (1 : Int) + d49320 p := by
  have ha := bounds6 p
  have hb := bounds49320 p
  omega
theorem compare47008 (p : Pattern) (guard : d0 p = 1) : d47633 p ≤ (1 : Int) + d47656 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47009 (p : Pattern) (guard : d15 p = 1) : d47634 p ≤ (1 : Int) + d49321 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47634, d49321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47007 p hg
    simpa only [d15, d47634, d49321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47634, d49321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47008 p hg
    simpa only [d15, d47634, d49321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47010 (p : Pattern) (guard : d45587 p = 1) : d47634 p ≤ (1 : Int) + d49321 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47006 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47009 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47011 (p : Pattern) (guard : d46472 p = 1) : d47634 p ≤ (1 : Int) + d49322 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47010 p hg
    simpa only [d46472, d49322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46782 p hg
    simpa only [d46472, d49322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47012 (p : Pattern) (guard : d369384 p = 1) : d47634 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d45588 p = 1 := by simpa only [d369384, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47005 p hg
    simpa only [d369384, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46472 p = 1 := by simpa only [d369384, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47011 p hg
    simpa only [d369384, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47013 (p : Pattern) (guard : d369385 p = 1) : d47634 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 223 with
  | false =>
    have hg : d369384 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47012 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47014 (p : Pattern) (guard : d369386 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369385 p = 1 := by simpa only [d369386, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47013 p hg
    simpa only [d369386, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369386, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46787 p hg
    simpa only [d369386, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47015 (p : Pattern) (guard : d369387 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369386 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47014 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46788 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47016 (p : Pattern) (guard : d369388 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47015 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275501 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46789 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47017 (p : Pattern) (guard : d369389 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369388 p = 1 := by simpa only [d369389, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47016 p hg
    simpa only [d369389, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369389, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46791 p hg
    simpa only [d369389, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47018 (p : Pattern) (guard : d369390 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47017 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46792 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47019 (p : Pattern) (guard : d369391 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369390 p = 1 := by simpa only [d369391, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47018 p hg
    simpa only [d369391, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369391, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369391, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47020 (p : Pattern) (guard : d369392 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369391 p = 1 := by simpa only [d369392, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47019 p hg
    simpa only [d369392, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369392, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369392, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47021 (p : Pattern) (guard : d369436 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369435 p = 1 := by simpa only [d369436, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46999 p hg
    simpa only [d369436, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369392 p = 1 := by simpa only [d369436, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47020 p hg
    simpa only [d369436, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47022 (p : Pattern) (guard : d369437 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369436 p = 1 := by simpa only [d369437, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47021 p hg
    simpa only [d369437, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369437, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d369437, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47023 (p : Pattern) (guard : d369438 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369437 p = 1 := by simpa only [d369438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47022 p hg
    simpa only [d369438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275549 p = 1 := by simpa only [d369438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46799 p hg
    simpa only [d369438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47024 (p : Pattern) (guard : d369439 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369438 p = 1 := by simpa only [d369439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47023 p hg
    simpa only [d369439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275550 p = 1 := by simpa only [d369439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46801 p hg
    simpa only [d369439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47025 (p : Pattern) (guard : d369440 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369439 p = 1 := by simpa only [d369440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47024 p hg
    simpa only [d369440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275551 p = 1 := by simpa only [d369440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46802 p hg
    simpa only [d369440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47026 (p : Pattern) (guard : d369441 p = 1) : d50734 p ≤ (1 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369441, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d369441, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369440 p = 1 := by simpa only [d369441, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47025 p hg
    simpa only [d369441, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47027 (p : Pattern) (guard : d369442 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369442, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d369442, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369441 p = 1 := by simpa only [d369442, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47026 p hg
    simpa only [d369442, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47028 (p : Pattern) (guard : d369443 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369442 p = 1 := by simpa only [d369443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47027 p hg
    simpa only [d369443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275554 p = 1 := by simpa only [d369443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46805 p hg
    simpa only [d369443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47029 (p : Pattern) (guard : d369444 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369443 p = 1 := by simpa only [d369444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47028 p hg
    simpa only [d369444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275555 p = 1 := by simpa only [d369444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46807 p hg
    simpa only [d369444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47030 (p : Pattern) (guard : d369445 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369444 p = 1 := by simpa only [d369445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47029 p hg
    simpa only [d369445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d369445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47031 (p : Pattern) (guard : d369446 p = 1) : d50737 p ≤ (1 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369445 p = 1 := by simpa only [d369446, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47030 p hg
    simpa only [d369446, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369446, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d369446, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47032 (p : Pattern) (guard : d369447 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369447, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369447, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369446 p = 1 := by simpa only [d369447, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47031 p hg
    simpa only [d369447, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47033 (p : Pattern) (guard : d369448 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369447 p = 1 := by simpa only [d369448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47032 p hg
    simpa only [d369448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275559 p = 1 := by simpa only [d369448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46812 p hg
    simpa only [d369448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47034 (p : Pattern) (guard : d369449 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369448 p = 1 := by simpa only [d369449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47033 p hg
    simpa only [d369449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47035 (p : Pattern) (guard : d369450 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369449 p = 1 := by simpa only [d369450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47034 p hg
    simpa only [d369450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47036 (p : Pattern) (guard : d369451 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369450 p = 1 := by simpa only [d369451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47035 p hg
    simpa only [d369451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47037 (p : Pattern) (guard : d369452 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369451 p = 1 := by simpa only [d369452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47036 p hg
    simpa only [d369452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275563 p = 1 := by simpa only [d369452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46816 p hg
    simpa only [d369452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47038 (p : Pattern) (guard : d369453 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369452 p = 1 := by simpa only [d369453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47037 p hg
    simpa only [d369453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47039 (p : Pattern) (guard : d369454 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369453 p = 1 := by simpa only [d369454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47038 p hg
    simpa only [d369454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275565 p = 1 := by simpa only [d369454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46818 p hg
    simpa only [d369454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47040 (p : Pattern) (guard : d369455 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369454 p = 1 := by simpa only [d369455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47039 p hg
    simpa only [d369455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47041 (p : Pattern) (guard : d369456 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369455 p = 1 := by simpa only [d369456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47040 p hg
    simpa only [d369456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47042 (p : Pattern) (guard : d369457 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369457, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369457, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369456 p = 1 := by simpa only [d369457, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47041 p hg
    simpa only [d369457, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47043 (p : Pattern) (guard : d369458 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369457 p = 1 := by simpa only [d369458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47042 p hg
    simpa only [d369458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47044 (p : Pattern) (guard : d369459 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369458 p = 1 := by simpa only [d369459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47043 p hg
    simpa only [d369459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47045 (p : Pattern) (guard : d369460 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369459 p = 1 := by simpa only [d369460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47044 p hg
    simpa only [d369460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47046 (p : Pattern) (guard : d369461 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 50 with
  | false =>
    have hg : d369460 p = 1 := by simpa only [d369461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47045 p hg
    simpa only [d369461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47047 (p : Pattern) (guard : d369462 p = 1) : d50822 p ≤ (1 : Int) + d367984 p := by
  cases selected : p 49 with
  | false =>
    have hg : d369461 p = 1 := by simpa only [d369462, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47046 p hg
    simpa only [d369462, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369462, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46827 p hg
    simpa only [d369462, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47048 (p : Pattern) (guard : d369463 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 48 with
  | false =>
    have hg : d369433 p = 1 := by simpa only [d369463, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46976 p hg
    simpa only [d369463, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369462 p = 1 := by simpa only [d369463, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47047 p hg
    simpa only [d369463, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47049 (p : Pattern) (guard : d369464 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369463 p = 1 := by simpa only [d369464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47048 p hg
    simpa only [d369464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47050 (p : Pattern) (guard : d369465 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369464 p = 1 := by simpa only [d369465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47049 p hg
    simpa only [d369465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47051 (p : Pattern) (guard : d369466 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369465 p = 1 := by simpa only [d369466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47050 p hg
    simpa only [d369466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47052 (p : Pattern) (guard : d369467 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369466 p = 1 := by simpa only [d369467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47051 p hg
    simpa only [d369467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47053 (p : Pattern) (guard : d369468 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369467 p = 1 := by simpa only [d369468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47052 p hg
    simpa only [d369468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47054 (p : Pattern) (guard : d369469 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d275580 p = 1 := by simpa only [d369469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46834 p hg
    simpa only [d369469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369468 p = 1 := by simpa only [d369469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47053 p hg
    simpa only [d369469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47055 (p : Pattern) (guard : d369470 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369409 p = 1 := by simpa only [d369470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46900 p hg
    simpa only [d369470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47056 (p : Pattern) (guard : d369471 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369470 p = 1 := by simpa only [d369471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47055 p hg
    simpa only [d369471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47057 (p : Pattern) (guard : d369472 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369471 p = 1 := by simpa only [d369472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47056 p hg
    simpa only [d369472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47058 (p : Pattern) (guard : d369473 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369472 p = 1 := by simpa only [d369473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47057 p hg
    simpa only [d369473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47059 (p : Pattern) (guard : d369474 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369473 p = 1 := by simpa only [d369474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47058 p hg
    simpa only [d369474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47060 (p : Pattern) (guard : d369475 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369474 p = 1 := by simpa only [d369475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47059 p hg
    simpa only [d369475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47061 (p : Pattern) (guard : d369476 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369475 p = 1 := by simpa only [d369476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47060 p hg
    simpa only [d369476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47062 (p : Pattern) (guard : d369477 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369416 p = 1 := by simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46916 p hg
    simpa only [d369477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47063 (p : Pattern) (guard : d369478 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369477 p = 1 := by simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47062 p hg
    simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47064 (p : Pattern) (guard : d369479 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369478 p = 1 := by simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47063 p hg
    simpa only [d369479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47065 (p : Pattern) (guard : d369480 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369479 p = 1 := by simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47064 p hg
    simpa only [d369480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47066 (p : Pattern) (guard : d369481 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369473 p = 1 := by simpa only [d369481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47058 p hg
    simpa only [d369481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369480 p = 1 := by simpa only [d369481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47065 p hg
    simpa only [d369481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47067 (p : Pattern) (guard : d369482 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369474 p = 1 := by simpa only [d369482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47059 p hg
    simpa only [d369482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369481 p = 1 := by simpa only [d369482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47066 p hg
    simpa only [d369482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47068 (p : Pattern) (guard : d369483 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369482 p = 1 := by simpa only [d369483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47067 p hg
    simpa only [d369483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47069 (p : Pattern) (guard : d369484 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369476 p = 1 := by simpa only [d369484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47061 p hg
    simpa only [d369484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369483 p = 1 := by simpa only [d369484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47068 p hg
    simpa only [d369484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47070 (p : Pattern) (guard : d369485 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369406 p = 1 := by simpa only [d369485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46897 p hg
    simpa only [d369485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47071 (p : Pattern) (guard : d369486 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369485 p = 1 := by simpa only [d369486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47070 p hg
    simpa only [d369486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47072 (p : Pattern) (guard : d369487 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369486 p = 1 := by simpa only [d369487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47071 p hg
    simpa only [d369487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275597 p = 1 := by simpa only [d369487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46851 p hg
    simpa only [d369487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47073 (p : Pattern) (guard : d369488 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369487 p = 1 := by simpa only [d369488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47072 p hg
    simpa only [d369488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47074 (p : Pattern) (guard : d369489 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369488 p = 1 := by simpa only [d369489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47073 p hg
    simpa only [d369489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47075 (p : Pattern) (guard : d369490 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369489 p = 1 := by simpa only [d369490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47074 p hg
    simpa only [d369490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47076 (p : Pattern) (guard : d369491 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369405 p = 1 := by simpa only [d369491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46896 p hg
    simpa only [d369491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47077 (p : Pattern) (guard : d369492 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369491 p = 1 := by simpa only [d369492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47076 p hg
    simpa only [d369492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47078 (p : Pattern) (guard : d369493 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369492 p = 1 := by simpa only [d369493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47077 p hg
    simpa only [d369493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47079 (p : Pattern) (guard : d369494 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369493 p = 1 := by simpa only [d369494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47078 p hg
    simpa only [d369494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275604 p = 1 := by simpa only [d369494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46858 p hg
    simpa only [d369494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47080 (p : Pattern) (guard : d369495 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369494 p = 1 := by simpa only [d369495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47079 p hg
    simpa only [d369495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47081 (p : Pattern) (guard : d369496 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369495 p = 1 := by simpa only [d369496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47080 p hg
    simpa only [d369496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47082 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (1 : Int) + d49392 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47083 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (1 : Int) + d47616 p := by
  have ha := bounds4 p
  have hb := bounds47616 p
  omega
theorem compare47084 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47085 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (1 : Int) + d47938 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, d47938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47083 p hg
    simpa only [d15, d47617, d47938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, d47938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47084 p hg
    simpa only [d15, d47617, d47938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47086 (p : Pattern) (guard : d45587 p = 1) : d47617 p ≤ (1 : Int) + d47938 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46873 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47085 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47087 (p : Pattern) (guard : d46040 p = 1) : d47617 p ≤ (1 : Int) + d49395 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46040, d49395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46868 p hg
    simpa only [d46040, d49395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d46040, d49395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47086 p hg
    simpa only [d46040, d49395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47088 (p : Pattern) (guard : d46041 p = 1) : d47617 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46041, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47082 p hg
    simpa only [d46041, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46040 p = 1 := by simpa only [d46041, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47087 p hg
    simpa only [d46041, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47089 (p : Pattern) (guard : d46042 p = 1) : d47617 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46041 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47088 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47090 (p : Pattern) (guard : d46043 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46042 p = 1 := by simpa only [d46043, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47089 p hg
    simpa only [d46043, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46043, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46656 p hg
    simpa only [d46043, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47091 (p : Pattern) (guard : d369497 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46043 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47090 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369386 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46877 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47092 (p : Pattern) (guard : d46459 p = 1) : d47617 p ≤ (1 : Int) + d49392 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d46459, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46862 p hg
    simpa only [d46459, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46459, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46651 p hg
    simpa only [d46459, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47093 (p : Pattern) (guard : d46460 p = 1) : d47617 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46459 p = 1 := by simpa only [d46460, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47092 p hg
    simpa only [d46460, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46460, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46653 p hg
    simpa only [d46460, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47094 (p : Pattern) (guard : d369498 p = 1) : d47617 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46460 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47093 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47095 (p : Pattern) (guard : d369499 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369498 p = 1 := by simpa only [d369499, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47094 p hg
    simpa only [d369499, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369499, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46656 p hg
    simpa only [d369499, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47096 (p : Pattern) (guard : d369500 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369499 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47095 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46657 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47097 (p : Pattern) (guard : d369501 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47091 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369500 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47096 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47098 (p : Pattern) (guard : d369502 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369501 p = 1 := by simpa only [d369502, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47097 p hg
    simpa only [d369502, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369502, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46660 p hg
    simpa only [d369502, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47099 (p : Pattern) (guard : d369503 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47098 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369389 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46880 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47100 (p : Pattern) (guard : d369504 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369503 p = 1 := by simpa only [d369504, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47099 p hg
    simpa only [d369504, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369504, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d369504, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47101 (p : Pattern) (guard : d369505 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369504 p = 1 := by simpa only [d369505, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47100 p hg
    simpa only [d369505, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369505, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d369505, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47102 (p : Pattern) (guard : d369506 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369506, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d369506, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369505 p = 1 := by simpa only [d369506, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47101 p hg
    simpa only [d369506, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47103 (p : Pattern) (guard : d369507 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369506 p = 1 := by simpa only [d369507, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47102 p hg
    simpa only [d369507, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369507, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d369507, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47104 (p : Pattern) (guard : d369508 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369507 p = 1 := by simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47103 p hg
    simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369394 p = 1 := by simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46885 p hg
    simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47105 (p : Pattern) (guard : d369509 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46878 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47106 (p : Pattern) (guard : d369510 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369509 p = 1 := by simpa only [d369510, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47105 p hg
    simpa only [d369510, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369510, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46660 p hg
    simpa only [d369510, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47107 (p : Pattern) (guard : d369511 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369510 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47106 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46661 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47108 (p : Pattern) (guard : d369512 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369511 p = 1 := by simpa only [d369512, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47107 p hg
    simpa only [d369512, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369512, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d369512, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47109 (p : Pattern) (guard : d369513 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369512 p = 1 := by simpa only [d369513, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47108 p hg
    simpa only [d369513, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369513, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d369513, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47110 (p : Pattern) (guard : d369514 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369514, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d369514, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369513 p = 1 := by simpa only [d369514, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47109 p hg
    simpa only [d369514, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47111 (p : Pattern) (guard : d369515 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369514 p = 1 := by simpa only [d369515, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47110 p hg
    simpa only [d369515, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369515, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d369515, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47112 (p : Pattern) (guard : d369516 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369515 p = 1 := by simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47111 p hg
    simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275508 p = 1 := by simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46670 p hg
    simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47113 (p : Pattern) (guard : d369517 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369508 p = 1 := by simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47104 p hg
    simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369516 p = 1 := by simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47112 p hg
    simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47114 (p : Pattern) (guard : d369518 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369517 p = 1 := by simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47113 p hg
    simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369396 p = 1 := by simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46887 p hg
    simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47115 (p : Pattern) (guard : d369519 p = 1) : d50577 p ≤ (1 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369519, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d369519, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369518 p = 1 := by simpa only [d369519, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47114 p hg
    simpa only [d369519, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47116 (p : Pattern) (guard : d369520 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369520, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d369520, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369519 p = 1 := by simpa only [d369520, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47115 p hg
    simpa only [d369520, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47117 (p : Pattern) (guard : d369521 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369520 p = 1 := by simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47116 p hg
    simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369399 p = 1 := by simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46890 p hg
    simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47118 (p : Pattern) (guard : d369522 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369521 p = 1 := by simpa only [d369522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47117 p hg
    simpa only [d369522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369400 p = 1 := by simpa only [d369522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46891 p hg
    simpa only [d369522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47119 (p : Pattern) (guard : d369523 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369522 p = 1 := by simpa only [d369523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47118 p hg
    simpa only [d369523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47120 (p : Pattern) (guard : d369524 p = 1) : d50590 p ≤ (1 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369523 p = 1 := by simpa only [d369524, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47119 p hg
    simpa only [d369524, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369524, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d369524, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47121 (p : Pattern) (guard : d369525 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369525, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369525, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369524 p = 1 := by simpa only [d369525, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47120 p hg
    simpa only [d369525, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47122 (p : Pattern) (guard : d369526 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369525 p = 1 := by simpa only [d369526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47121 p hg
    simpa only [d369526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369404 p = 1 := by simpa only [d369526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46895 p hg
    simpa only [d369526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47123 (p : Pattern) (guard : d369527 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369526 p = 1 := by simpa only [d369527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47122 p hg
    simpa only [d369527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47124 (p : Pattern) (guard : d369528 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369527 p = 1 := by simpa only [d369528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47123 p hg
    simpa only [d369528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47125 (p : Pattern) (guard : d369529 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369528 p = 1 := by simpa only [d369529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47124 p hg
    simpa only [d369529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47126 (p : Pattern) (guard : d369530 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369529 p = 1 := by simpa only [d369530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47125 p hg
    simpa only [d369530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369408 p = 1 := by simpa only [d369530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46899 p hg
    simpa only [d369530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47127 (p : Pattern) (guard : d369531 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369530 p = 1 := by simpa only [d369531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47126 p hg
    simpa only [d369531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47128 (p : Pattern) (guard : d369532 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369404 p = 1 := by simpa only [d369532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46895 p hg
    simpa only [d369532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47129 (p : Pattern) (guard : d369533 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369532 p = 1 := by simpa only [d369533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47128 p hg
    simpa only [d369533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47130 (p : Pattern) (guard : d369534 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369533 p = 1 := by simpa only [d369534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47129 p hg
    simpa only [d369534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47131 (p : Pattern) (guard : d369535 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369534 p = 1 := by simpa only [d369535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47130 p hg
    simpa only [d369535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47132 (p : Pattern) (guard : d369536 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369535 p = 1 := by simpa only [d369536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47131 p hg
    simpa only [d369536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47133 (p : Pattern) (guard : d369537 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369536 p = 1 := by simpa only [d369537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47132 p hg
    simpa only [d369537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47134 (p : Pattern) (guard : d369538 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369531 p = 1 := by simpa only [d369538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47127 p hg
    simpa only [d369538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369537 p = 1 := by simpa only [d369538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47133 p hg
    simpa only [d369538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47135 (p : Pattern) (guard : d369539 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d369496 p = 1 := by simpa only [d369539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47081 p hg
    simpa only [d369539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369538 p = 1 := by simpa only [d369539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47134 p hg
    simpa only [d369539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47136 (p : Pattern) (guard : d369540 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d369490 p = 1 := by simpa only [d369540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47075 p hg
    simpa only [d369540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369539 p = 1 := by simpa only [d369540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47135 p hg
    simpa only [d369540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47137 (p : Pattern) (guard : d369541 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369540 p = 1 := by simpa only [d369541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47136 p hg
    simpa only [d369541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47138 (p : Pattern) (guard : d369542 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369485 p = 1 := by simpa only [d369542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47070 p hg
    simpa only [d369542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47139 (p : Pattern) (guard : d369543 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369542 p = 1 := by simpa only [d369543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47138 p hg
    simpa only [d369543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275641 p = 1 := by simpa only [d369543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46906 p hg
    simpa only [d369543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47140 (p : Pattern) (guard : d369544 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369543 p = 1 := by simpa only [d369544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47139 p hg
    simpa only [d369544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47141 (p : Pattern) (guard : d369545 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369544 p = 1 := by simpa only [d369545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47140 p hg
    simpa only [d369545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47142 (p : Pattern) (guard : d369546 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369545 p = 1 := by simpa only [d369546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47141 p hg
    simpa only [d369546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47143 (p : Pattern) (guard : d369547 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369492 p = 1 := by simpa only [d369547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47077 p hg
    simpa only [d369547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47144 (p : Pattern) (guard : d369548 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369547 p = 1 := by simpa only [d369548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47143 p hg
    simpa only [d369548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275646 p = 1 := by simpa only [d369548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46911 p hg
    simpa only [d369548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47145 (p : Pattern) (guard : d369549 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369548 p = 1 := by simpa only [d369549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47144 p hg
    simpa only [d369549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47146 (p : Pattern) (guard : d369550 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369549 p = 1 := by simpa only [d369550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47145 p hg
    simpa only [d369550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47147 (p : Pattern) (guard : d369551 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369528 p = 1 := by simpa only [d369551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47124 p hg
    simpa only [d369551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47148 (p : Pattern) (guard : d369552 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369551 p = 1 := by simpa only [d369552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47147 p hg
    simpa only [d369552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369415 p = 1 := by simpa only [d369552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46915 p hg
    simpa only [d369552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47149 (p : Pattern) (guard : d369553 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369552 p = 1 := by simpa only [d369553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47148 p hg
    simpa only [d369553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47150 (p : Pattern) (guard : d369554 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369534 p = 1 := by simpa only [d369554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47130 p hg
    simpa only [d369554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47151 (p : Pattern) (guard : d369555 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369554 p = 1 := by simpa only [d369555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47150 p hg
    simpa only [d369555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47152 (p : Pattern) (guard : d369556 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369555 p = 1 := by simpa only [d369556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47151 p hg
    simpa only [d369556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47153 (p : Pattern) (guard : d369557 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369553 p = 1 := by simpa only [d369557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47149 p hg
    simpa only [d369557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369556 p = 1 := by simpa only [d369557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47152 p hg
    simpa only [d369557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47154 (p : Pattern) (guard : d369558 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d369550 p = 1 := by simpa only [d369558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47146 p hg
    simpa only [d369558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369557 p = 1 := by simpa only [d369558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47153 p hg
    simpa only [d369558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47155 (p : Pattern) (guard : d369559 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d369546 p = 1 := by simpa only [d369559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47142 p hg
    simpa only [d369559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369558 p = 1 := by simpa only [d369559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47154 p hg
    simpa only [d369559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47156 (p : Pattern) (guard : d369560 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369540 p = 1 := by simpa only [d369560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47136 p hg
    simpa only [d369560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369559 p = 1 := by simpa only [d369560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47155 p hg
    simpa only [d369560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47157 (p : Pattern) (guard : d369561 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369541 p = 1 := by simpa only [d369561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47137 p hg
    simpa only [d369561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369560 p = 1 := by simpa only [d369561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47156 p hg
    simpa only [d369561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47158 (p : Pattern) (guard : d369562 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369473 p = 1 := by simpa only [d369562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47058 p hg
    simpa only [d369562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275584 p = 1 := by simpa only [d369562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46838 p hg
    simpa only [d369562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47159 (p : Pattern) (guard : d369563 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369562 p = 1 := by simpa only [d369563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47158 p hg
    simpa only [d369563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275592 p = 1 := by simpa only [d369563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46846 p hg
    simpa only [d369563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47160 (p : Pattern) (guard : d369564 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369561 p = 1 := by simpa only [d369564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47157 p hg
    simpa only [d369564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369563 p = 1 := by simpa only [d369564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47159 p hg
    simpa only [d369564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47161 (p : Pattern) (guard : d369565 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369564 p = 1 := by simpa only [d369565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47160 p hg
    simpa only [d369565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47162 (p : Pattern) (guard : d369566 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 50 with
  | false =>
    have hg : d369484 p = 1 := by simpa only [d369566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47069 p hg
    simpa only [d369566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369565 p = 1 := by simpa only [d369566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47161 p hg
    simpa only [d369566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47163 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (1 : Int) + d49561 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47164 (p : Pattern) (guard : d14 p = 1) : d5 p ≤ (1 : Int) + d47705 p := by
  have ha := bounds5 p
  have hb := bounds47705 p
  omega
theorem compare47165 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47166 (p : Pattern) (guard : d15 p = 1) : d47706 p ≤ (1 : Int) + d47947 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47706, d47947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47164 p hg
    simpa only [d15, d47706, d47947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47706, d47947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47165 p hg
    simpa only [d15, d47706, d47947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47167 (p : Pattern) (guard : d45587 p = 1) : d47706 p ≤ (1 : Int) + d47947 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46939 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47166 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47168 (p : Pattern) (guard : d46040 p = 1) : d47706 p ≤ (1 : Int) + d49564 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46040, d49564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46934 p hg
    simpa only [d46040, d49564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d46040, d49564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47167 p hg
    simpa only [d46040, d49564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47169 (p : Pattern) (guard : d46041 p = 1) : d47706 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46041, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47163 p hg
    simpa only [d46041, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46040 p = 1 := by simpa only [d46041, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47168 p hg
    simpa only [d46041, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47170 (p : Pattern) (guard : d46042 p = 1) : d47706 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46041 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47169 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47171 (p : Pattern) (guard : d46043 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46042 p = 1 := by simpa only [d46043, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47170 p hg
    simpa only [d46043, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46043, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46717 p hg
    simpa only [d46043, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47172 (p : Pattern) (guard : d369497 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46043 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47171 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369386 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46943 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47173 (p : Pattern) (guard : d46459 p = 1) : d47706 p ≤ (1 : Int) + d49561 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d46459, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46928 p hg
    simpa only [d46459, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46459, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46712 p hg
    simpa only [d46459, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47174 (p : Pattern) (guard : d46460 p = 1) : d47706 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46459 p = 1 := by simpa only [d46460, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47173 p hg
    simpa only [d46460, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46460, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46714 p hg
    simpa only [d46460, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47175 (p : Pattern) (guard : d369498 p = 1) : d47706 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46460 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47174 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47176 (p : Pattern) (guard : d369499 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369498 p = 1 := by simpa only [d369499, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47175 p hg
    simpa only [d369499, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369499, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46717 p hg
    simpa only [d369499, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47177 (p : Pattern) (guard : d369500 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369499 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47176 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46718 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47178 (p : Pattern) (guard : d369501 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47172 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369500 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47177 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47179 (p : Pattern) (guard : d369502 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369501 p = 1 := by simpa only [d369502, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47178 p hg
    simpa only [d369502, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369502, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46721 p hg
    simpa only [d369502, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47180 (p : Pattern) (guard : d369503 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47179 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369389 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46946 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47181 (p : Pattern) (guard : d369504 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369503 p = 1 := by simpa only [d369504, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47180 p hg
    simpa only [d369504, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369504, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369504, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47182 (p : Pattern) (guard : d369505 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369504 p = 1 := by simpa only [d369505, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47181 p hg
    simpa only [d369505, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369505, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369505, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47183 (p : Pattern) (guard : d369506 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369506, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d369506, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369505 p = 1 := by simpa only [d369506, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47182 p hg
    simpa only [d369506, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47184 (p : Pattern) (guard : d369507 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369506 p = 1 := by simpa only [d369507, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47183 p hg
    simpa only [d369507, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369507, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d369507, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47185 (p : Pattern) (guard : d369508 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369507 p = 1 := by simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47184 p hg
    simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369394 p = 1 := by simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46951 p hg
    simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47186 (p : Pattern) (guard : d369509 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46944 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47187 (p : Pattern) (guard : d369510 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369509 p = 1 := by simpa only [d369510, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47186 p hg
    simpa only [d369510, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369510, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46721 p hg
    simpa only [d369510, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47188 (p : Pattern) (guard : d369511 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369510 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47187 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46722 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47189 (p : Pattern) (guard : d369512 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369511 p = 1 := by simpa only [d369512, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47188 p hg
    simpa only [d369512, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369512, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369512, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47190 (p : Pattern) (guard : d369513 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369512 p = 1 := by simpa only [d369513, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47189 p hg
    simpa only [d369513, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369513, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369513, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47191 (p : Pattern) (guard : d369514 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369514, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d369514, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369513 p = 1 := by simpa only [d369514, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47190 p hg
    simpa only [d369514, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47192 (p : Pattern) (guard : d369515 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369514 p = 1 := by simpa only [d369515, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47191 p hg
    simpa only [d369515, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369515, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d369515, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47193 (p : Pattern) (guard : d369516 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369515 p = 1 := by simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47192 p hg
    simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275508 p = 1 := by simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46730 p hg
    simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47194 (p : Pattern) (guard : d369517 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369508 p = 1 := by simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47185 p hg
    simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369516 p = 1 := by simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47193 p hg
    simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47195 (p : Pattern) (guard : d369518 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369517 p = 1 := by simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47194 p hg
    simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369396 p = 1 := by simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46953 p hg
    simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47196 (p : Pattern) (guard : d369519 p = 1) : d50664 p ≤ (1 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369519, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d369519, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369518 p = 1 := by simpa only [d369519, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47195 p hg
    simpa only [d369519, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47197 (p : Pattern) (guard : d369520 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369520, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d369520, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369519 p = 1 := by simpa only [d369520, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47196 p hg
    simpa only [d369520, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47198 (p : Pattern) (guard : d369521 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369520 p = 1 := by simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47197 p hg
    simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369399 p = 1 := by simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46956 p hg
    simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47199 (p : Pattern) (guard : d369522 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369521 p = 1 := by simpa only [d369522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47198 p hg
    simpa only [d369522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369400 p = 1 := by simpa only [d369522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46957 p hg
    simpa only [d369522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47200 (p : Pattern) (guard : d369523 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369522 p = 1 := by simpa only [d369523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47199 p hg
    simpa only [d369523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47201 (p : Pattern) (guard : d369524 p = 1) : d50673 p ≤ (1 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369523 p = 1 := by simpa only [d369524, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47200 p hg
    simpa only [d369524, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369524, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d369524, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47202 (p : Pattern) (guard : d369525 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369525, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d369525, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369524 p = 1 := by simpa only [d369525, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47201 p hg
    simpa only [d369525, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47203 (p : Pattern) (guard : d369526 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369525 p = 1 := by simpa only [d369526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47202 p hg
    simpa only [d369526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369404 p = 1 := by simpa only [d369526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46961 p hg
    simpa only [d369526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47204 (p : Pattern) (guard : d369527 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369526 p = 1 := by simpa only [d369527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47203 p hg
    simpa only [d369527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47205 (p : Pattern) (guard : d369528 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369527 p = 1 := by simpa only [d369528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47204 p hg
    simpa only [d369528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47206 (p : Pattern) (guard : d369551 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369528 p = 1 := by simpa only [d369551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47205 p hg
    simpa only [d369551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47207 (p : Pattern) (guard : d369552 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369551 p = 1 := by simpa only [d369552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47206 p hg
    simpa only [d369552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369415 p = 1 := by simpa only [d369552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46965 p hg
    simpa only [d369552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47208 (p : Pattern) (guard : d369553 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369552 p = 1 := by simpa only [d369553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47207 p hg
    simpa only [d369553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47209 (p : Pattern) (guard : d369532 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369404 p = 1 := by simpa only [d369532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46961 p hg
    simpa only [d369532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47210 (p : Pattern) (guard : d369533 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369532 p = 1 := by simpa only [d369533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47209 p hg
    simpa only [d369533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47211 (p : Pattern) (guard : d369534 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369533 p = 1 := by simpa only [d369534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47210 p hg
    simpa only [d369534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47212 (p : Pattern) (guard : d369554 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369534 p = 1 := by simpa only [d369554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47211 p hg
    simpa only [d369554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47213 (p : Pattern) (guard : d369555 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369554 p = 1 := by simpa only [d369555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47212 p hg
    simpa only [d369555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47214 (p : Pattern) (guard : d369556 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369555 p = 1 := by simpa only [d369556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47213 p hg
    simpa only [d369556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47215 (p : Pattern) (guard : d369557 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369553 p = 1 := by simpa only [d369557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47208 p hg
    simpa only [d369557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369556 p = 1 := by simpa only [d369557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47214 p hg
    simpa only [d369557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47216 (p : Pattern) (guard : d369567 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369557 p = 1 := by simpa only [d369567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47215 p hg
    simpa only [d369567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47217 (p : Pattern) (guard : d369568 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369567 p = 1 := by simpa only [d369568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47216 p hg
    simpa only [d369568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47218 (p : Pattern) (guard : d369569 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369569, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369569, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369568 p = 1 := by simpa only [d369569, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47217 p hg
    simpa only [d369569, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47219 (p : Pattern) (guard : d369570 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369569 p = 1 := by simpa only [d369570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47218 p hg
    simpa only [d369570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47220 (p : Pattern) (guard : d275588 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275530 p = 1 := by simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46748 p hg
    simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47221 (p : Pattern) (guard : d275589 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275588 p = 1 := by simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47220 p hg
    simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47222 (p : Pattern) (guard : d275590 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275589 p = 1 := by simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47221 p hg
    simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47223 (p : Pattern) (guard : d275591 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275590 p = 1 := by simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47222 p hg
    simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47224 (p : Pattern) (guard : d275820 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275820, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275820, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275591 p = 1 := by simpa only [d275820, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47223 p hg
    simpa only [d275820, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47225 (p : Pattern) (guard : d275821 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d275821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275820 p = 1 := by simpa only [d275821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47224 p hg
    simpa only [d275821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47226 (p : Pattern) (guard : d369571 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369570 p = 1 := by simpa only [d369571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47219 p hg
    simpa only [d369571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275821 p = 1 := by simpa only [d369571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47225 p hg
    simpa only [d369571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47227 (p : Pattern) (guard : d369572 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369571 p = 1 := by simpa only [d369572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47226 p hg
    simpa only [d369572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47228 (p : Pattern) (guard : d369573 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 50 with
  | false =>
    have hg : d369572 p = 1 := by simpa only [d369573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47227 p hg
    simpa only [d369573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47229 (p : Pattern) (guard : d369574 p = 1) : d50676 p ≤ (1 : Int) + d367880 p := by
  cases selected : p 49 with
  | false =>
    have hg : d369566 p = 1 := by simpa only [d369574, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47162 p hg
    simpa only [d369574, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369573 p = 1 := by simpa only [d369574, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47228 p hg
    simpa only [d369574, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47230 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (1 : Int) + d49311 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47231 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (1 : Int) + d47629 p := by
  have ha := bounds2 p
  have hb := bounds47629 p
  omega
theorem compare47232 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (1 : Int) + d47638 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47233 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (1 : Int) + d49314 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d49314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47231 p hg
    simpa only [d15, d47630, d49314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d49314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47232 p hg
    simpa only [d15, d47630, d49314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47234 (p : Pattern) (guard : d45587 p = 1) : d47630 p ≤ (1 : Int) + d49314 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46988 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47233 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47235 (p : Pattern) (guard : d46040 p = 1) : d47630 p ≤ (1 : Int) + d49315 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46040, d49315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46983 p hg
    simpa only [d46040, d49315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d46040, d49315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47234 p hg
    simpa only [d46040, d49315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47236 (p : Pattern) (guard : d46041 p = 1) : d47630 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46041, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47230 p hg
    simpa only [d46041, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46040 p = 1 := by simpa only [d46041, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47235 p hg
    simpa only [d46041, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47237 (p : Pattern) (guard : d46042 p = 1) : d47630 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46041 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47236 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47238 (p : Pattern) (guard : d46043 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46042 p = 1 := by simpa only [d46043, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47237 p hg
    simpa only [d46043, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46043, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46770 p hg
    simpa only [d46043, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47239 (p : Pattern) (guard : d369497 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46043 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47238 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369386 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46992 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47240 (p : Pattern) (guard : d46459 p = 1) : d47630 p ≤ (1 : Int) + d49311 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d46459, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46977 p hg
    simpa only [d46459, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46459, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46765 p hg
    simpa only [d46459, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47241 (p : Pattern) (guard : d46460 p = 1) : d47630 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46459 p = 1 := by simpa only [d46460, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47240 p hg
    simpa only [d46460, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46460, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46767 p hg
    simpa only [d46460, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47242 (p : Pattern) (guard : d369498 p = 1) : d47630 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46460 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47241 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47243 (p : Pattern) (guard : d369499 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369498 p = 1 := by simpa only [d369499, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47242 p hg
    simpa only [d369499, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369499, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46770 p hg
    simpa only [d369499, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47244 (p : Pattern) (guard : d369500 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369499 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47243 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46771 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47245 (p : Pattern) (guard : d369501 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47239 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369500 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47244 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47246 (p : Pattern) (guard : d369502 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369501 p = 1 := by simpa only [d369502, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47245 p hg
    simpa only [d369502, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369502, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46774 p hg
    simpa only [d369502, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47247 (p : Pattern) (guard : d369503 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47246 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369389 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46995 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47248 (p : Pattern) (guard : d369575 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369575, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d369575, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369503 p = 1 := by simpa only [d369575, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47247 p hg
    simpa only [d369575, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47249 (p : Pattern) (guard : d369504 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369503 p = 1 := by simpa only [d369504, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47099 p hg
    simpa only [d369504, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369504, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369504, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
