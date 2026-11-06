import NetHack.Soko22Hazard87.Compare021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5500 (p : Pattern) (guard : d6884 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d4921 p = 1 := by simpa only [d6884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5499 p hg
    simpa only [d6884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d6884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5409 p hg
    simpa only [d6884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5501 (p : Pattern) (guard : d6885 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6884 p = 1 := by simpa only [d6885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5500 p hg
    simpa only [d6885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5502 (p : Pattern) (guard : d6886 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6885 p = 1 := by simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5501 p hg
    simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5503 (p : Pattern) (guard : d6887 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6886 p = 1 := by simpa only [d6887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5502 p hg
    simpa only [d6887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5504 (p : Pattern) (guard : d6888 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6883 p = 1 := by simpa only [d6888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5495 p hg
    simpa only [d6888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6887 p = 1 := by simpa only [d6888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5503 p hg
    simpa only [d6888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5505 (p : Pattern) (guard : d82107 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6888 p = 1 := by simpa only [d82107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5504 p hg
    simpa only [d82107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5506 (p : Pattern) (guard : d6115 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d771 p = 1 := by simpa only [d6115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5405 p hg
    simpa only [d6115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5507 (p : Pattern) (guard : d6116 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6115 p = 1 := by simpa only [d6116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5506 p hg
    simpa only [d6116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5508 (p : Pattern) (guard : d6117 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6116 p = 1 := by simpa only [d6117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5507 p hg
    simpa only [d6117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5509 (p : Pattern) (guard : d6118 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6117 p = 1 := by simpa only [d6118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5508 p hg
    simpa only [d6118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5510 (p : Pattern) (guard : d6160 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6118 p = 1 := by simpa only [d6160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5509 p hg
    simpa only [d6160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5511 (p : Pattern) (guard : d6161 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6160 p = 1 := by simpa only [d6161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5510 p hg
    simpa only [d6161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5512 (p : Pattern) (guard : d82108 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82107 p = 1 := by simpa only [d82108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5505 p hg
    simpa only [d82108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6161 p = 1 := by simpa only [d82108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5511 p hg
    simpa only [d82108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5513 (p : Pattern) (guard : d82109 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d82109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5453 p hg
    simpa only [d82109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82108 p = 1 := by simpa only [d82109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5512 p hg
    simpa only [d82109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5514 (p : Pattern) (guard : d82110 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d810 p = 1 := by simpa only [d82110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5444 p hg
    simpa only [d82110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82109 p = 1 := by simpa only [d82110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5513 p hg
    simpa only [d82110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5515 (p : Pattern) (guard : d82111 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82110 p = 1 := by simpa only [d82111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d82111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5516 (p : Pattern) (guard : d915 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d803 p = 1 := by simpa only [d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5437 p hg
    simpa only [d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5517 (p : Pattern) (guard : d916 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d805 p = 1 := by simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5439 p hg
    simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5518 (p : Pattern) (guard : d917 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5516 p hg
    simpa only [d917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5517 p hg
    simpa only [d917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5519 (p : Pattern) (guard : d918 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5518 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5520 (p : Pattern) (guard : d919 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5519 p hg
    simpa only [d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5521 (p : Pattern) (guard : d920 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d919 p = 1 := by simpa only [d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5520 p hg
    simpa only [d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5522 (p : Pattern) (guard : d921 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d812 p = 1 := by simpa only [d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5446 p hg
    simpa only [d921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5523 (p : Pattern) (guard : d922 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d815 p = 1 := by simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5524 (p : Pattern) (guard : d923 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d921 p = 1 := by simpa only [d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5522 p hg
    simpa only [d923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d922 p = 1 := by simpa only [d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5523 p hg
    simpa only [d923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5525 (p : Pattern) (guard : d924 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d923 p = 1 := by simpa only [d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5524 p hg
    simpa only [d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5526 (p : Pattern) (guard : d925 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d924 p = 1 := by simpa only [d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5525 p hg
    simpa only [d925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5527 (p : Pattern) (guard : d6894 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6882 p = 1 := by simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5494 p hg
    simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5528 (p : Pattern) (guard : d6895 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6886 p = 1 := by simpa only [d6895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5502 p hg
    simpa only [d6895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5529 (p : Pattern) (guard : d6896 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6894 p = 1 := by simpa only [d6896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5527 p hg
    simpa only [d6896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6895 p = 1 := by simpa only [d6896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5528 p hg
    simpa only [d6896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5530 (p : Pattern) (guard : d82112 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6896 p = 1 := by simpa only [d82112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5529 p hg
    simpa only [d82112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5531 (p : Pattern) (guard : d6127 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6117 p = 1 := by simpa only [d6127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5508 p hg
    simpa only [d6127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5532 (p : Pattern) (guard : d6181 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6127 p = 1 := by simpa only [d6181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5531 p hg
    simpa only [d6181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5533 (p : Pattern) (guard : d6182 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6181 p = 1 := by simpa only [d6182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5532 p hg
    simpa only [d6182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5534 (p : Pattern) (guard : d82113 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82112 p = 1 := by simpa only [d82113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5530 p hg
    simpa only [d82113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6182 p = 1 := by simpa only [d82113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5533 p hg
    simpa only [d82113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5535 (p : Pattern) (guard : d82114 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d925 p = 1 := by simpa only [d82114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5526 p hg
    simpa only [d82114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82113 p = 1 := by simpa only [d82114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5534 p hg
    simpa only [d82114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5536 (p : Pattern) (guard : d82115 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d920 p = 1 := by simpa only [d82115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5521 p hg
    simpa only [d82115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82114 p = 1 := by simpa only [d82115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5535 p hg
    simpa only [d82115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5537 (p : Pattern) (guard : d82116 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d82110 p = 1 := by simpa only [d82116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d82116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82115 p = 1 := by simpa only [d82116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5536 p hg
    simpa only [d82116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5538 (p : Pattern) (guard : d82117 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d82111 p = 1 := by simpa only [d82117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5515 p hg
    simpa only [d82117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82116 p = 1 := by simpa only [d82117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5537 p hg
    simpa only [d82117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5539 (p : Pattern) (guard : d6903 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6887 p = 1 := by simpa only [d6903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5503 p hg
    simpa only [d6903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d6903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5417 p hg
    simpa only [d6903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5540 (p : Pattern) (guard : d6904 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6903 p = 1 := by simpa only [d6904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5539 p hg
    simpa only [d6904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5541 (p : Pattern) (guard : d6905 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d6904 p = 1 := by simpa only [d6905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5540 p hg
    simpa only [d6905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5542 (p : Pattern) (guard : d6906 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6905 p = 1 := by simpa only [d6906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5541 p hg
    simpa only [d6906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5543 (p : Pattern) (guard : d6907 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6906 p = 1 := by simpa only [d6907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5542 p hg
    simpa only [d6907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5544 (p : Pattern) (guard : d939 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d783 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5417 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5545 (p : Pattern) (guard : d940 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d939 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5544 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5546 (p : Pattern) (guard : d941 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d940 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5545 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5547 (p : Pattern) (guard : d942 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d941 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5546 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5548 (p : Pattern) (guard : d943 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d942 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5547 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5549 (p : Pattern) (guard : d6908 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6907 p = 1 := by simpa only [d6908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5543 p hg
    simpa only [d6908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d943 p = 1 := by simpa only [d6908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5548 p hg
    simpa only [d6908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5550 (p : Pattern) (guard : d945 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5427 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5551 (p : Pattern) (guard : d946 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d945 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5550 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5552 (p : Pattern) (guard : d947 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d946 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5551 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5553 (p : Pattern) (guard : d948 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d947 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5552 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5554 (p : Pattern) (guard : d949 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d948 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5553 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5555 (p : Pattern) (guard : d950 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d943 p = 1 := by simpa only [d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5548 p hg
    simpa only [d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d949 p = 1 := by simpa only [d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5554 p hg
    simpa only [d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5556 (p : Pattern) (guard : d6909 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d6908 p = 1 := by simpa only [d6909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5549 p hg
    simpa only [d6909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d950 p = 1 := by simpa only [d6909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5555 p hg
    simpa only [d6909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5557 (p : Pattern) (guard : d82118 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82117 p = 1 := by simpa only [d82118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5538 p hg
    simpa only [d82118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6909 p = 1 := by simpa only [d82118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5556 p hg
    simpa only [d82118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5558 (p : Pattern) (guard : d82119 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82118 p = 1 := by simpa only [d82119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5557 p hg
    simpa only [d82119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5559 (p : Pattern) (guard : d82120 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d802 p = 1 := by simpa only [d82120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5436 p hg
    simpa only [d82120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82119 p = 1 := by simpa only [d82120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5558 p hg
    simpa only [d82120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5560 (p : Pattern) (guard : d820 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5184 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5561 (p : Pattern) (guard : d821 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5560 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5185 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5562 (p : Pattern) (guard : d822 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5561 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5563 (p : Pattern) (guard : d823 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5562 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5564 (p : Pattern) (guard : d824 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d532 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5188 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5565 (p : Pattern) (guard : d825 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4887 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5566 (p : Pattern) (guard : d826 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5184 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5565 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5567 (p : Pattern) (guard : d827 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5566 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5191 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5568 (p : Pattern) (guard : d828 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5567 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5569 (p : Pattern) (guard : d829 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5568 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5570 (p : Pattern) (guard : d830 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5569 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5194 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5571 (p : Pattern) (guard : d831 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d824 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5564 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5570 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5572 (p : Pattern) (guard : d832 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d832, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5571 p hg
    simpa only [d832, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d832, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d832, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5573 (p : Pattern) (guard : d833 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d832 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5572 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d541 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5197 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5574 (p : Pattern) (guard : d834 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5573 p hg
    simpa only [d834, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d834, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5575 (p : Pattern) (guard : d835 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d834 p = 1 := by simpa only [d835, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5574 p hg
    simpa only [d835, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d835, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5576 (p : Pattern) (guard : d836 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5575 p hg
    simpa only [d836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5577 (p : Pattern) (guard : d837 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d837, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5576 p hg
    simpa only [d837, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d837, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d837, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5578 (p : Pattern) (guard : d838 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d837 p = 1 := by simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5577 p hg
    simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d546 p = 1 := by simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5202 p hg
    simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5579 (p : Pattern) (guard : d839 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d838 p = 1 := by simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5578 p hg
    simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d547 p = 1 := by simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5203 p hg
    simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5580 (p : Pattern) (guard : d750 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4689 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5581 (p : Pattern) (guard : d751 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5580 p hg
    simpa only [d751, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d751, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5582 (p : Pattern) (guard : d752 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5581 p hg
    simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5583 (p : Pattern) (guard : d753 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5582 p hg
    simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5584 (p : Pattern) (guard : d754 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5583 p hg
    simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5585 (p : Pattern) (guard : d755 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4900 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5584 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5586 (p : Pattern) (guard : d756 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d547 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5203 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d755 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5585 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5587 (p : Pattern) (guard : d840 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d839 p = 1 := by simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5579 p hg
    simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d756 p = 1 := by simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5586 p hg
    simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5588 (p : Pattern) (guard : d841 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d841, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d841, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d840 p = 1 := by simpa only [d841, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5587 p hg
    simpa only [d841, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5589 (p : Pattern) (guard : d842 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d842, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d842, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d842, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5588 p hg
    simpa only [d842, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5590 (p : Pattern) (guard : d757 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5584 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5591 (p : Pattern) (guard : d758 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5585 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5590 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5592 (p : Pattern) (guard : d759 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d756 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5586 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5591 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5593 (p : Pattern) (guard : d760 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d760, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d760, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d760, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5592 p hg
    simpa only [d760, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5594 (p : Pattern) (guard : d761 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d761, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d761, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d760 p = 1 := by simpa only [d761, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5593 p hg
    simpa only [d761, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5595 (p : Pattern) (guard : d843 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d842 p = 1 := by simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5589 p hg
    simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d761 p = 1 := by simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5594 p hg
    simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5596 (p : Pattern) (guard : d762 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5590 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5597 (p : Pattern) (guard : d763 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5591 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5596 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5598 (p : Pattern) (guard : d764 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d764, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5597 p hg
    simpa only [d764, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5599 (p : Pattern) (guard : d765 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d765, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5598 p hg
    simpa only [d765, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5600 (p : Pattern) (guard : d766 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d761 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5594 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5599 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5601 (p : Pattern) (guard : d844 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d843 p = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5595 p hg
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d766 p = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5600 p hg
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5602 (p : Pattern) (guard : d845 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d844 p = 1 := by simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5601 p hg
    simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5603 (p : Pattern) (guard : d846 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d846, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5602 p hg
    simpa only [d846, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d846, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d846, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5604 (p : Pattern) (guard : d847 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d847, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d847, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d846 p = 1 := by simpa only [d847, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5603 p hg
    simpa only [d847, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5605 (p : Pattern) (guard : d6875 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d761 p = 1 := by simpa only [d6875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5594 p hg
    simpa only [d6875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d6875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5606 (p : Pattern) (guard : d4913 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d4913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5585 p hg
    simpa only [d4913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d4913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5607 (p : Pattern) (guard : d4914 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d4913 p = 1 := by simpa only [d4914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5606 p hg
    simpa only [d4914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d4914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5596 p hg
    simpa only [d4914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5608 (p : Pattern) (guard : d4915 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4915, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d4915, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4914 p = 1 := by simpa only [d4915, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5607 p hg
    simpa only [d4915, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5609 (p : Pattern) (guard : d4916 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4916, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d4916, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4915 p = 1 := by simpa only [d4916, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5608 p hg
    simpa only [d4916, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5610 (p : Pattern) (guard : d4917 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d4916 p = 1 := by simpa only [d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5609 p hg
    simpa only [d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5611 (p : Pattern) (guard : d6876 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d6875 p = 1 := by simpa only [d6876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5605 p hg
    simpa only [d6876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4917 p = 1 := by simpa only [d6876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5610 p hg
    simpa only [d6876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5612 (p : Pattern) (guard : d6877 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6876 p = 1 := by simpa only [d6877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5611 p hg
    simpa only [d6877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d6877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5613 (p : Pattern) (guard : d6878 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6877 p = 1 := by simpa only [d6878, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5612 p hg
    simpa only [d6878, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6878, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d6878, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5614 (p : Pattern) (guard : d6879 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6879, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d6879, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6878 p = 1 := by simpa only [d6879, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5613 p hg
    simpa only [d6879, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5615 (p : Pattern) (guard : d6880 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d847 p = 1 := by simpa only [d6880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5604 p hg
    simpa only [d6880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6879 p = 1 := by simpa only [d6880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5614 p hg
    simpa only [d6880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5616 (p : Pattern) (guard : d6881 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6880 p = 1 := by simpa only [d6881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5615 p hg
    simpa only [d6881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5617 (p : Pattern) (guard : d6882 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6881 p = 1 := by simpa only [d6882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5616 p hg
    simpa only [d6882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5618 (p : Pattern) (guard : d6894 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6882 p = 1 := by simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5617 p hg
    simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5619 (p : Pattern) (guard : d4918 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d766 p = 1 := by simpa only [d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5600 p hg
    simpa only [d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4917 p = 1 := by simpa only [d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5610 p hg
    simpa only [d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5620 (p : Pattern) (guard : d4919 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d4918 p = 1 := by simpa only [d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5619 p hg
    simpa only [d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5621 (p : Pattern) (guard : d4920 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4919 p = 1 := by simpa only [d4920, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5620 p hg
    simpa only [d4920, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4920, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d4920, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5622 (p : Pattern) (guard : d4921 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4921, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d4921, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4920 p = 1 := by simpa only [d4921, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5621 p hg
    simpa only [d4921, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5623 (p : Pattern) (guard : d767 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5599 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5624 (p : Pattern) (guard : d772 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5623 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5625 (p : Pattern) (guard : d773 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5624 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5626 (p : Pattern) (guard : d774 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5625 p hg
    simpa only [d774, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d774, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5627 (p : Pattern) (guard : d775 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d775, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5626 p hg
    simpa only [d775, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5628 (p : Pattern) (guard : d6884 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d4921 p = 1 := by simpa only [d6884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5622 p hg
    simpa only [d6884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d6884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5627 p hg
    simpa only [d6884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5629 (p : Pattern) (guard : d6885 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6884 p = 1 := by simpa only [d6885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5628 p hg
    simpa only [d6885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5630 (p : Pattern) (guard : d6886 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6885 p = 1 := by simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5629 p hg
    simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5631 (p : Pattern) (guard : d6895 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6886 p = 1 := by simpa only [d6895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5630 p hg
    simpa only [d6895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5632 (p : Pattern) (guard : d6896 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6894 p = 1 := by simpa only [d6896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5618 p hg
    simpa only [d6896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6895 p = 1 := by simpa only [d6896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5631 p hg
    simpa only [d6896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5633 (p : Pattern) (guard : d82112 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6896 p = 1 := by simpa only [d82112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5632 p hg
    simpa only [d82112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5634 (p : Pattern) (guard : d768 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d766 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5600 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5623 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5635 (p : Pattern) (guard : d769 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5634 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5636 (p : Pattern) (guard : d770 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d770, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5635 p hg
    simpa only [d770, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d770, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5637 (p : Pattern) (guard : d771 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d771, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d771, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5636 p hg
    simpa only [d771, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5638 (p : Pattern) (guard : d6115 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d771 p = 1 := by simpa only [d6115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5637 p hg
    simpa only [d6115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5639 (p : Pattern) (guard : d6116 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6115 p = 1 := by simpa only [d6116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5638 p hg
    simpa only [d6116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5640 (p : Pattern) (guard : d6117 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6116 p = 1 := by simpa only [d6117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5639 p hg
    simpa only [d6117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5641 (p : Pattern) (guard : d6127 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6117 p = 1 := by simpa only [d6127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5640 p hg
    simpa only [d6127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5642 (p : Pattern) (guard : d6181 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6127 p = 1 := by simpa only [d6181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5641 p hg
    simpa only [d6181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5643 (p : Pattern) (guard : d6182 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6181 p = 1 := by simpa only [d6182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5642 p hg
    simpa only [d6182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5644 (p : Pattern) (guard : d82113 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82112 p = 1 := by simpa only [d82113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5633 p hg
    simpa only [d82113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6182 p = 1 := by simpa only [d82113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5643 p hg
    simpa only [d82113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5645 (p : Pattern) (guard : d82121 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82113 p = 1 := by simpa only [d82121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5644 p hg
    simpa only [d82121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5646 (p : Pattern) (guard : d82122 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82121 p = 1 := by simpa only [d82122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5645 p hg
    simpa only [d82122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5647 (p : Pattern) (guard : d82123 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82123, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82123, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82122 p = 1 := by simpa only [d82123, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5646 p hg
    simpa only [d82123, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5648 (p : Pattern) (guard : d82124 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82123 p = 1 := by simpa only [d82124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5647 p hg
    simpa only [d82124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5649 (p : Pattern) (guard : d780 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5627 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5650 (p : Pattern) (guard : d781 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5649 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5651 (p : Pattern) (guard : d782 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5650 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5652 (p : Pattern) (guard : d793 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5651 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5653 (p : Pattern) (guard : d945 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5652 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5654 (p : Pattern) (guard : d946 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d945 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5653 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5655 (p : Pattern) (guard : d947 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d946 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5654 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5656 (p : Pattern) (guard : d948 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d947 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5655 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5657 (p : Pattern) (guard : d949 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d948 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5656 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5658 (p : Pattern) (guard : d959 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d959, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d959, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d949 p = 1 := by simpa only [d959, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5657 p hg
    simpa only [d959, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5659 (p : Pattern) (guard : d960 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d959 p = 1 := by simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5660 (p : Pattern) (guard : d82125 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82124 p = 1 := by simpa only [d82125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5648 p hg
    simpa only [d82125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d960 p = 1 := by simpa only [d82125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5659 p hg
    simpa only [d82125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5661 (p : Pattern) (guard : d82126 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82125 p = 1 := by simpa only [d82126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5660 p hg
    simpa only [d82126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5662 (p : Pattern) (guard : d82127 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82126 p = 1 := by simpa only [d82127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5661 p hg
    simpa only [d82127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5663 (p : Pattern) (guard : d82128 p = 1) : d47768 p ≤ (-1 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82120 p = 1 := by simpa only [d82128, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5559 p hg
    simpa only [d82128, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82127 p = 1 := by simpa only [d82128, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d82128, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5664 (p : Pattern) (guard : d820 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5271 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5665 (p : Pattern) (guard : d821 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5664 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5272 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5666 (p : Pattern) (guard : d822 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5665 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5667 (p : Pattern) (guard : d823 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5666 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5668 (p : Pattern) (guard : d824 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5667 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d532 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5275 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5669 (p : Pattern) (guard : d825 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4946 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5670 (p : Pattern) (guard : d826 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5271 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5671 (p : Pattern) (guard : d827 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5278 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5672 (p : Pattern) (guard : d828 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5671 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5673 (p : Pattern) (guard : d829 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5672 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5674 (p : Pattern) (guard : d830 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5281 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5675 (p : Pattern) (guard : d831 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d824 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5668 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5674 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5676 (p : Pattern) (guard : d832 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d832, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5675 p hg
    simpa only [d832, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d832, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d832, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5677 (p : Pattern) (guard : d833 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d832 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5676 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d541 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5284 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5678 (p : Pattern) (guard : d965 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d965, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d965, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d833 p = 1 := by simpa only [d965, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5677 p hg
    simpa only [d965, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5679 (p : Pattern) (guard : d834 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5467 p hg
    simpa only [d834, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d834, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5680 (p : Pattern) (guard : d966 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d965 p = 1 := by simpa only [d966, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d966, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d834 p = 1 := by simpa only [d966, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5679 p hg
    simpa only [d966, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5681 (p : Pattern) (guard : d820 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5289 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5682 (p : Pattern) (guard : d821 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5681 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5683 (p : Pattern) (guard : d822 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5682 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5684 (p : Pattern) (guard : d823 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5683 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5685 (p : Pattern) (guard : d824 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d532 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5293 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5686 (p : Pattern) (guard : d825 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4962 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5687 (p : Pattern) (guard : d826 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5289 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5688 (p : Pattern) (guard : d827 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5687 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5296 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5689 (p : Pattern) (guard : d828 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5688 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5690 (p : Pattern) (guard : d829 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5691 (p : Pattern) (guard : d830 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5299 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5692 (p : Pattern) (guard : d831 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d824 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5685 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5691 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5693 (p : Pattern) (guard : d832 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d832, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5692 p hg
    simpa only [d832, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d832, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d832, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5694 (p : Pattern) (guard : d833 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d832 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5693 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d541 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5302 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5695 (p : Pattern) (guard : d834 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5694 p hg
    simpa only [d834, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d834, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5696 (p : Pattern) (guard : d835 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d834 p = 1 := by simpa only [d835, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5695 p hg
    simpa only [d835, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d835, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5697 (p : Pattern) (guard : d967 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d966 p = 1 := by simpa only [d967, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5680 p hg
    simpa only [d967, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d967, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5696 p hg
    simpa only [d967, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5698 (p : Pattern) (guard : d968 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d967 p = 1 := by simpa only [d968, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5697 p hg
    simpa only [d968, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d968, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d968, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5699 (p : Pattern) (guard : d969 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d968 p = 1 := by simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d662 p = 1 := by simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5307 p hg
    simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5700 (p : Pattern) (guard : d970 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d969 p = 1 := by simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5699 p hg
    simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d663 p = 1 := by simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5308 p hg
    simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5701 (p : Pattern) (guard : d750 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5702 (p : Pattern) (guard : d971 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d971, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d971, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d750 p = 1 := by simpa only [d971, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d971, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5703 (p : Pattern) (guard : d751 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d751, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d751, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5704 (p : Pattern) (guard : d972 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d971 p = 1 := by simpa only [d972, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5702 p hg
    simpa only [d972, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d751 p = 1 := by simpa only [d972, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d972, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5705 (p : Pattern) (guard : d750 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4747 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5706 (p : Pattern) (guard : d751 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5705 p hg
    simpa only [d751, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d751, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5707 (p : Pattern) (guard : d752 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5706 p hg
    simpa only [d752, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d752, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5708 (p : Pattern) (guard : d973 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d972 p = 1 := by simpa only [d973, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5704 p hg
    simpa only [d973, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d973, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5707 p hg
    simpa only [d973, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5709 (p : Pattern) (guard : d974 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d973 p = 1 := by simpa only [d974, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5708 p hg
    simpa only [d974, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d974, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d974, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5710 (p : Pattern) (guard : d975 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d415 p = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4975 p hg
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d974 p = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5709 p hg
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5711 (p : Pattern) (guard : d976 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d663 p = 1 := by simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5308 p hg
    simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d975 p = 1 := by simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5712 (p : Pattern) (guard : d977 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d970 p = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5700 p hg
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d976 p = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5711 p hg
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5713 (p : Pattern) (guard : d978 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d978, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d978, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d977 p = 1 := by simpa only [d978, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5712 p hg
    simpa only [d978, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5714 (p : Pattern) (guard : d979 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d979, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d979, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d978 p = 1 := by simpa only [d979, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5713 p hg
    simpa only [d979, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5715 (p : Pattern) (guard : d980 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d974 p = 1 := by simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5709 p hg
    simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5716 (p : Pattern) (guard : d981 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d975 p = 1 := by simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d980 p = 1 := by simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5715 p hg
    simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5717 (p : Pattern) (guard : d982 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d976 p = 1 := by simpa only [d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5711 p hg
    simpa only [d982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d981 p = 1 := by simpa only [d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5716 p hg
    simpa only [d982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5718 (p : Pattern) (guard : d983 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d983, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d983, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d982 p = 1 := by simpa only [d983, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5717 p hg
    simpa only [d983, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5719 (p : Pattern) (guard : d984 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d984, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d984, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d983 p = 1 := by simpa only [d984, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5718 p hg
    simpa only [d984, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5720 (p : Pattern) (guard : d985 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d979 p = 1 := by simpa only [d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5719 p hg
    simpa only [d985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5721 (p : Pattern) (guard : d986 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d980 p = 1 := by simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5715 p hg
    simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5722 (p : Pattern) (guard : d987 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d981 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5716 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5721 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5723 (p : Pattern) (guard : d988 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d988, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d988, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d988, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5722 p hg
    simpa only [d988, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5724 (p : Pattern) (guard : d989 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d989, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d989, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d988 p = 1 := by simpa only [d989, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5723 p hg
    simpa only [d989, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5725 (p : Pattern) (guard : d990 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5719 p hg
    simpa only [d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d989 p = 1 := by simpa only [d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5724 p hg
    simpa only [d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5726 (p : Pattern) (guard : d991 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5720 p hg
    simpa only [d991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d990 p = 1 := by simpa only [d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5725 p hg
    simpa only [d991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5727 (p : Pattern) (guard : d992 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d991 p = 1 := by simpa only [d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5726 p hg
    simpa only [d992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5728 (p : Pattern) (guard : d993 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d992 p = 1 := by simpa only [d993, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5727 p hg
    simpa only [d993, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d993, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d993, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5729 (p : Pattern) (guard : d994 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d994, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d994, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d993 p = 1 := by simpa only [d994, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5728 p hg
    simpa only [d994, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5730 (p : Pattern) (guard : d6921 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d6921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5719 p hg
    simpa only [d6921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5731 (p : Pattern) (guard : d6210 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d975 p = 1 := by simpa only [d6210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d6210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5732 (p : Pattern) (guard : d6211 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d6210 p = 1 := by simpa only [d6211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5731 p hg
    simpa only [d6211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d6211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5721 p hg
    simpa only [d6211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5733 (p : Pattern) (guard : d6212 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6212, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d6212, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6211 p = 1 := by simpa only [d6212, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5732 p hg
    simpa only [d6212, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5734 (p : Pattern) (guard : d6213 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6213, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d6213, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6212 p = 1 := by simpa only [d6213, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5733 p hg
    simpa only [d6213, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5735 (p : Pattern) (guard : d6214 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d6213 p = 1 := by simpa only [d6214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5734 p hg
    simpa only [d6214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5736 (p : Pattern) (guard : d6922 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d6921 p = 1 := by simpa only [d6922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5730 p hg
    simpa only [d6922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6214 p = 1 := by simpa only [d6922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d6922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5737 (p : Pattern) (guard : d6923 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6922 p = 1 := by simpa only [d6923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5736 p hg
    simpa only [d6923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5738 (p : Pattern) (guard : d6924 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6923 p = 1 := by simpa only [d6924, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5737 p hg
    simpa only [d6924, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6924, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d6924, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5739 (p : Pattern) (guard : d6925 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6925, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6925, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6924 p = 1 := by simpa only [d6925, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5738 p hg
    simpa only [d6925, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5740 (p : Pattern) (guard : d6926 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d994 p = 1 := by simpa only [d6926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5729 p hg
    simpa only [d6926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6925 p = 1 := by simpa only [d6926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5739 p hg
    simpa only [d6926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5741 (p : Pattern) (guard : d6927 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6926 p = 1 := by simpa only [d6927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5740 p hg
    simpa only [d6927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5742 (p : Pattern) (guard : d6928 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6927 p = 1 := by simpa only [d6928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5741 p hg
    simpa only [d6928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5743 (p : Pattern) (guard : d6929 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6928 p = 1 := by simpa only [d6929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5742 p hg
    simpa only [d6929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5744 (p : Pattern) (guard : d6215 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d990 p = 1 := by simpa only [d6215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5725 p hg
    simpa only [d6215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6214 p = 1 := by simpa only [d6215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d6215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5745 (p : Pattern) (guard : d6216 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6215 p = 1 := by simpa only [d6216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5744 p hg
    simpa only [d6216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5746 (p : Pattern) (guard : d6217 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6216 p = 1 := by simpa only [d6217, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5745 p hg
    simpa only [d6217, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6217, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d6217, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5747 (p : Pattern) (guard : d6218 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6218, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6218, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6217 p = 1 := by simpa only [d6218, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5746 p hg
    simpa only [d6218, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5748 (p : Pattern) (guard : d995 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d989 p = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5724 p hg
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5749 (p : Pattern) (guard : d1004 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d995 p = 1 := by simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5748 p hg
    simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
