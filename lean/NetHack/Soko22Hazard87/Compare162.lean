import NetHack.Soko22Hazard87.Compare161
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40500 (p : Pattern) (guard : d325091 p = 1) : d50734 p ≤ (1 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325091, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39939 p hg
    simpa only [d325091, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325090 p = 1 := by simpa only [d325091, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40499 p hg
    simpa only [d325091, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40501 (p : Pattern) (guard : d325092 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325092, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39938 p hg
    simpa only [d325092, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325091 p = 1 := by simpa only [d325092, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40500 p hg
    simpa only [d325092, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40502 (p : Pattern) (guard : d325093 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d325092 p = 1 := by simpa only [d325093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40501 p hg
    simpa only [d325093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d325093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40503 (p : Pattern) (guard : d325094 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d325059 p = 1 := by simpa only [d325094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40463 p hg
    simpa only [d325094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325093 p = 1 := by simpa only [d325094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40502 p hg
    simpa only [d325094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40504 (p : Pattern) (guard : d325095 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d325094 p = 1 := by simpa only [d325095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40503 p hg
    simpa only [d325095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d325095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40505 (p : Pattern) (guard : d325096 p = 1) : d50737 p ≤ (1 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d325095 p = 1 := by simpa only [d325096, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40504 p hg
    simpa only [d325096, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325096, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40026 p hg
    simpa only [d325096, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40506 (p : Pattern) (guard : d325097 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325097, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d325097, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325096 p = 1 := by simpa only [d325097, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40505 p hg
    simpa only [d325097, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40507 (p : Pattern) (guard : d325098 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d325097 p = 1 := by simpa only [d325098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40506 p hg
    simpa only [d325098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40508 (p : Pattern) (guard : d325099 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d325098 p = 1 := by simpa only [d325099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40507 p hg
    simpa only [d325099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40509 (p : Pattern) (guard : d325100 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d325099 p = 1 := by simpa only [d325100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40508 p hg
    simpa only [d325100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40510 (p : Pattern) (guard : d325101 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d325100 p = 1 := by simpa only [d325101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40509 p hg
    simpa only [d325101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40511 (p : Pattern) (guard : d325102 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 91 with
  | false =>
    have hg : d325101 p = 1 := by simpa only [d325102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40510 p hg
    simpa only [d325102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40512 (p : Pattern) (guard : d325103 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 90 with
  | false =>
    have hg : d325102 p = 1 := by simpa only [d325103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40511 p hg
    simpa only [d325103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40513 (p : Pattern) (guard : d325104 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325082 p = 1 := by simpa only [d325104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40486 p hg
    simpa only [d325104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325103 p = 1 := by simpa only [d325104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40512 p hg
    simpa only [d325104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40514 (p : Pattern) (guard : d325105 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325104 p = 1 := by simpa only [d325105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40513 p hg
    simpa only [d325105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40515 (p : Pattern) (guard : d325106 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325105 p = 1 := by simpa only [d325106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40514 p hg
    simpa only [d325106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40516 (p : Pattern) (guard : d325107 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325107, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325107, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325106 p = 1 := by simpa only [d325107, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40515 p hg
    simpa only [d325107, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40517 (p : Pattern) (guard : d325108 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39936 p hg
    simpa only [d325108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325107 p = 1 := by simpa only [d325108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40516 p hg
    simpa only [d325108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40518 (p : Pattern) (guard : d325109 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d325076 p = 1 := by simpa only [d325109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40480 p hg
    simpa only [d325109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40519 (p : Pattern) (guard : d325110 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d325109 p = 1 := by simpa only [d325110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40518 p hg
    simpa only [d325110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40520 (p : Pattern) (guard : d325111 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d325110 p = 1 := by simpa only [d325111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40519 p hg
    simpa only [d325111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40521 (p : Pattern) (guard : d325112 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d325111 p = 1 := by simpa only [d325112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40520 p hg
    simpa only [d325112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40522 (p : Pattern) (guard : d325113 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 91 with
  | false =>
    have hg : d325112 p = 1 := by simpa only [d325113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40521 p hg
    simpa only [d325113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40523 (p : Pattern) (guard : d325114 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325113 p = 1 := by simpa only [d325114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40522 p hg
    simpa only [d325114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40524 (p : Pattern) (guard : d325115 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325114 p = 1 := by simpa only [d325115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40523 p hg
    simpa only [d325115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40525 (p : Pattern) (guard : d325116 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325115 p = 1 := by simpa only [d325116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40524 p hg
    simpa only [d325116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40526 (p : Pattern) (guard : d325117 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325116 p = 1 := by simpa only [d325117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40525 p hg
    simpa only [d325117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40527 (p : Pattern) (guard : d325118 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325118, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325118, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325117 p = 1 := by simpa only [d325118, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40526 p hg
    simpa only [d325118, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40528 (p : Pattern) (guard : d325119 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39936 p hg
    simpa only [d325119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325118 p = 1 := by simpa only [d325119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40527 p hg
    simpa only [d325119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40529 (p : Pattern) (guard : d325120 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 69 with
  | false =>
    have hg : d325108 p = 1 := by simpa only [d325120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40517 p hg
    simpa only [d325120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325119 p = 1 := by simpa only [d325120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40528 p hg
    simpa only [d325120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40530 (p : Pattern) (guard : d325121 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 51 with
  | false =>
    have hg : d325120 p = 1 := by simpa only [d325121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40529 p hg
    simpa only [d325121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39936 p hg
    simpa only [d325121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40531 (p : Pattern) (guard : d325122 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 50 with
  | false =>
    have hg : d325121 p = 1 := by simpa only [d325122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40530 p hg
    simpa only [d325122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39936 p hg
    simpa only [d325122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40532 (p : Pattern) (guard : d325123 p = 1) : d50822 p ≤ (1 : Int) + d324610 p := by
  cases selected : p 49 with
  | false =>
    have hg : d325122 p = 1 := by simpa only [d325123, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40531 p hg
    simpa only [d325123, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325123, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40093 p hg
    simpa only [d325123, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40533 (p : Pattern) (guard : d325124 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 48 with
  | false =>
    have hg : d325039 p = 1 := by simpa only [d325124, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40391 p hg
    simpa only [d325124, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325123 p = 1 := by simpa only [d325124, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40532 p hg
    simpa only [d325124, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40534 (p : Pattern) (guard : d325125 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325124 p = 1 := by simpa only [d325125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40533 p hg
    simpa only [d325125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40535 (p : Pattern) (guard : d325126 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325125 p = 1 := by simpa only [d325126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40534 p hg
    simpa only [d325126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40536 (p : Pattern) (guard : d325127 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325126 p = 1 := by simpa only [d325127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40535 p hg
    simpa only [d325127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40537 (p : Pattern) (guard : d325128 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325127 p = 1 := by simpa only [d325128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40536 p hg
    simpa only [d325128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40538 (p : Pattern) (guard : d325129 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325128 p = 1 := by simpa only [d325129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40537 p hg
    simpa only [d325129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40539 (p : Pattern) (guard : d325130 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325129 p = 1 := by simpa only [d325130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40538 p hg
    simpa only [d325130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40540 (p : Pattern) (guard : d325131 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325130 p = 1 := by simpa only [d325131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40539 p hg
    simpa only [d325131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40541 (p : Pattern) (guard : d325132 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325131 p = 1 := by simpa only [d325132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40540 p hg
    simpa only [d325132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40542 (p : Pattern) (guard : d325133 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325132 p = 1 := by simpa only [d325133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40541 p hg
    simpa only [d325133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40543 (p : Pattern) (guard : d325134 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325133 p = 1 := by simpa only [d325134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40542 p hg
    simpa only [d325134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40544 (p : Pattern) (guard : d325135 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d324881 p = 1 := by simpa only [d325135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40105 p hg
    simpa only [d325135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325134 p = 1 := by simpa only [d325135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40543 p hg
    simpa only [d325135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40545 (p : Pattern) (guard : d325136 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 260 with
  | false =>
    have hg : d325135 p = 1 := by simpa only [d325136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40544 p hg
    simpa only [d325136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40546 (p : Pattern) (guard : d325137 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 259 with
  | false =>
    have hg : d325136 p = 1 := by simpa only [d325137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40545 p hg
    simpa only [d325137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40547 (p : Pattern) (guard : d325138 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 258 with
  | false =>
    have hg : d325137 p = 1 := by simpa only [d325138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40546 p hg
    simpa only [d325138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40548 (p : Pattern) (guard : d325139 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 257 with
  | false =>
    have hg : d325138 p = 1 := by simpa only [d325139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40547 p hg
    simpa only [d325139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40549 (p : Pattern) (guard : d325140 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 256 with
  | false =>
    have hg : d325139 p = 1 := by simpa only [d325140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40548 p hg
    simpa only [d325140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40550 (p : Pattern) (guard : d325141 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 255 with
  | false =>
    have hg : d325140 p = 1 := by simpa only [d325141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40549 p hg
    simpa only [d325141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40551 (p : Pattern) (guard : d325142 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 254 with
  | false =>
    have hg : d325141 p = 1 := by simpa only [d325142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40550 p hg
    simpa only [d325142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40552 (p : Pattern) (guard : d325143 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 253 with
  | false =>
    have hg : d325142 p = 1 := by simpa only [d325143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40551 p hg
    simpa only [d325143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40553 (p : Pattern) (guard : d325144 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 252 with
  | false =>
    have hg : d325143 p = 1 := by simpa only [d325144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40552 p hg
    simpa only [d325144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40554 (p : Pattern) (guard : d325145 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 251 with
  | false =>
    have hg : d325144 p = 1 := by simpa only [d325145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40553 p hg
    simpa only [d325145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40555 (p : Pattern) (guard : d325146 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 250 with
  | false =>
    have hg : d325145 p = 1 := by simpa only [d325146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40554 p hg
    simpa only [d325146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40556 (p : Pattern) (guard : d325147 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 249 with
  | false =>
    have hg : d325146 p = 1 := by simpa only [d325147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40555 p hg
    simpa only [d325147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40557 (p : Pattern) (guard : d325148 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 245 with
  | false =>
    have hg : d325147 p = 1 := by simpa only [d325148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40556 p hg
    simpa only [d325148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40558 (p : Pattern) (guard : d325149 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 200 with
  | false =>
    have hg : d325148 p = 1 := by simpa only [d325149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40557 p hg
    simpa only [d325149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40559 (p : Pattern) (guard : d325150 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 199 with
  | false =>
    have hg : d325149 p = 1 := by simpa only [d325150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40558 p hg
    simpa only [d325150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40560 (p : Pattern) (guard : d325151 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 186 with
  | false =>
    have hg : d325150 p = 1 := by simpa only [d325151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40559 p hg
    simpa only [d325151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40561 (p : Pattern) (guard : d325152 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 185 with
  | false =>
    have hg : d325151 p = 1 := by simpa only [d325152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40560 p hg
    simpa only [d325152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40562 (p : Pattern) (guard : d325153 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 184 with
  | false =>
    have hg : d325152 p = 1 := by simpa only [d325153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40561 p hg
    simpa only [d325153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40563 (p : Pattern) (guard : d325154 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 181 with
  | false =>
    have hg : d325153 p = 1 := by simpa only [d325154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40562 p hg
    simpa only [d325154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40564 (p : Pattern) (guard : d325155 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 177 with
  | false =>
    have hg : d325154 p = 1 := by simpa only [d325155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40563 p hg
    simpa only [d325155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40565 (p : Pattern) (guard : d325156 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 164 with
  | false =>
    have hg : d325155 p = 1 := by simpa only [d325156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40564 p hg
    simpa only [d325156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40566 (p : Pattern) (guard : d325157 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 156 with
  | false =>
    have hg : d325156 p = 1 := by simpa only [d325157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40565 p hg
    simpa only [d325157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40567 (p : Pattern) (guard : d325158 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 155 with
  | false =>
    have hg : d325157 p = 1 := by simpa only [d325158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40566 p hg
    simpa only [d325158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40568 (p : Pattern) (guard : d325159 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 134 with
  | false =>
    have hg : d325158 p = 1 := by simpa only [d325159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40567 p hg
    simpa only [d325159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40569 (p : Pattern) (guard : d325160 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 133 with
  | false =>
    have hg : d325159 p = 1 := by simpa only [d325160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40568 p hg
    simpa only [d325160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40570 (p : Pattern) (guard : d325161 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 120 with
  | false =>
    have hg : d325160 p = 1 := by simpa only [d325161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40569 p hg
    simpa only [d325161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40571 (p : Pattern) (guard : d325162 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 118 with
  | false =>
    have hg : d325161 p = 1 := by simpa only [d325162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40570 p hg
    simpa only [d325162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40572 (p : Pattern) (guard : d325163 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 114 with
  | false =>
    have hg : d325162 p = 1 := by simpa only [d325163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40571 p hg
    simpa only [d325163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40573 (p : Pattern) (guard : d325164 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 111 with
  | false =>
    have hg : d325163 p = 1 := by simpa only [d325164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40572 p hg
    simpa only [d325164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40574 (p : Pattern) (guard : d325165 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 98 with
  | false =>
    have hg : d325164 p = 1 := by simpa only [d325165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40573 p hg
    simpa only [d325165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40575 (p : Pattern) (guard : d325166 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 97 with
  | false =>
    have hg : d325165 p = 1 := by simpa only [d325166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40574 p hg
    simpa only [d325166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40576 (p : Pattern) (guard : d325167 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 94 with
  | false =>
    have hg : d325166 p = 1 := by simpa only [d325167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40575 p hg
    simpa only [d325167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40577 (p : Pattern) (guard : d325168 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 76 with
  | false =>
    have hg : d325167 p = 1 := by simpa only [d325168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40576 p hg
    simpa only [d325168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40578 (p : Pattern) (guard : d325169 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 67 with
  | false =>
    have hg : d325168 p = 1 := by simpa only [d325169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40577 p hg
    simpa only [d325169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40579 (p : Pattern) (guard : d325170 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 52 with
  | false =>
    have hg : d325169 p = 1 := by simpa only [d325170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40578 p hg
    simpa only [d325170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40580 (p : Pattern) (guard : d325171 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 47 with
  | false =>
    have hg : d325170 p = 1 := by simpa only [d325171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40579 p hg
    simpa only [d325171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40581 (p : Pattern) (guard : d325172 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 46 with
  | false =>
    have hg : d325171 p = 1 := by simpa only [d325172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40580 p hg
    simpa only [d325172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40582 (p : Pattern) (guard : d325173 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 45 with
  | false =>
    have hg : d325172 p = 1 := by simpa only [d325173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40581 p hg
    simpa only [d325173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40583 (p : Pattern) (guard : d325174 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 30 with
  | false =>
    have hg : d325173 p = 1 := by simpa only [d325174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40582 p hg
    simpa only [d325174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40584 (p : Pattern) (guard : d325175 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 29 with
  | false =>
    have hg : d325174 p = 1 := by simpa only [d325175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40583 p hg
    simpa only [d325175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40585 (p : Pattern) (guard : d325176 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 28 with
  | false =>
    have hg : d325175 p = 1 := by simpa only [d325176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40584 p hg
    simpa only [d325176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40586 (p : Pattern) (guard : d325177 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 27 with
  | false =>
    have hg : d325176 p = 1 := by simpa only [d325177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40585 p hg
    simpa only [d325177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40587 (p : Pattern) (guard : d325178 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 25 with
  | false =>
    have hg : d325177 p = 1 := by simpa only [d325178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40586 p hg
    simpa only [d325178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d325178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40588 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40589 (p : Pattern) (guard : d0 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40590 (p : Pattern) (guard : d0 p = 1) : d50588 p ≤ (0 : Int) + d324470 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40591 (p : Pattern) (guard : d0 p = 1) : d50546 p ≤ (0 : Int) + d324444 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40592 (p : Pattern) (guard : d0 p = 1) : d50566 p ≤ (0 : Int) + d324451 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40593 (p : Pattern) (guard : d0 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40594 (p : Pattern) (guard : d0 p = 1) : d50569 p ≤ (0 : Int) + d324454 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40595 (p : Pattern) (guard : d0 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40596 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (0 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40597 (p : Pattern) (guard : d32155 p = 1) : d49396 p ≤ (0 : Int) + d49396 p := by
  omega
theorem compare40598 (p : Pattern) (guard : d324612 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324612, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d324612, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d324612, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40597 p hg
    simpa only [d324612, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40599 (p : Pattern) (guard : d0 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40600 (p : Pattern) (guard : d324613 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d324612 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40598 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40601 (p : Pattern) (guard : d324614 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d324613 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40600 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40602 (p : Pattern) (guard : d0 p = 1) : d49397 p ≤ (0 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40603 (p : Pattern) (guard : d324615 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 182 with
  | false =>
    have hg : d324614 p = 1 := by simpa only [d324615, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40601 p hg
    simpa only [d324615, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324615, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40602 p hg
    simpa only [d324615, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40604 (p : Pattern) (guard : d324616 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40595 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324615 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40603 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40605 (p : Pattern) (guard : d0 p = 1) : d50527 p ≤ (0 : Int) + d49351 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40606 (p : Pattern) (guard : d324617 p = 1) : d50570 p ≤ (0 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324616 p = 1 := by simpa only [d324617, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40604 p hg
    simpa only [d324617, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324617, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40605 p hg
    simpa only [d324617, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40607 (p : Pattern) (guard : d0 p = 1) : d50531 p ≤ (0 : Int) + d324430 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40608 (p : Pattern) (guard : d324618 p = 1) : d50571 p ≤ (0 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324617 p = 1 := by simpa only [d324618, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40606 p hg
    simpa only [d324618, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324618, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40607 p hg
    simpa only [d324618, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40609 (p : Pattern) (guard : d324619 p = 1) : d50572 p ≤ (0 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324619, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40594 p hg
    simpa only [d324619, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324618 p = 1 := by simpa only [d324619, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40608 p hg
    simpa only [d324619, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40610 (p : Pattern) (guard : d0 p = 1) : d50575 p ≤ (0 : Int) + d324442 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40611 (p : Pattern) (guard : d324620 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324619 p = 1 := by simpa only [d324620, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40609 p hg
    simpa only [d324620, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324620, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40610 p hg
    simpa only [d324620, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40612 (p : Pattern) (guard : d324621 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40593 p hg
    simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324620 p = 1 := by simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40611 p hg
    simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40613 (p : Pattern) (guard : d1115 p = 1) : d49396 p ≤ (0 : Int) + d49396 p := by
  omega
theorem compare40614 (p : Pattern) (guard : d221076 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221076, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d221076, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d221076, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40613 p hg
    simpa only [d221076, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40615 (p : Pattern) (guard : d221096 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221076 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40614 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40616 (p : Pattern) (guard : d19 p = 1) : d49396 p ≤ (0 : Int) + d49396 p := by
  omega
theorem compare40617 (p : Pattern) (guard : d221097 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221097, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d221097, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d221097, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40616 p hg
    simpa only [d221097, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40618 (p : Pattern) (guard : d221098 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221097 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40617 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40619 (p : Pattern) (guard : d221099 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221096 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40615 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221098 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40618 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40620 (p : Pattern) (guard : d221100 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221099 p = 1 := by simpa only [d221100, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40619 p hg
    simpa only [d221100, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221100, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40602 p hg
    simpa only [d221100, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40621 (p : Pattern) (guard : d324622 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40603 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221100 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40620 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40622 (p : Pattern) (guard : d324623 p = 1) : d50570 p ≤ (0 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324622 p = 1 := by simpa only [d324623, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40621 p hg
    simpa only [d324623, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324623, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40605 p hg
    simpa only [d324623, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40623 (p : Pattern) (guard : d324624 p = 1) : d50571 p ≤ (0 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324623 p = 1 := by simpa only [d324624, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40622 p hg
    simpa only [d324624, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324624, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40607 p hg
    simpa only [d324624, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40624 (p : Pattern) (guard : d324625 p = 1) : d50572 p ≤ (0 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324625, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40594 p hg
    simpa only [d324625, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324624 p = 1 := by simpa only [d324625, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40623 p hg
    simpa only [d324625, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40625 (p : Pattern) (guard : d324626 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324625 p = 1 := by simpa only [d324626, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40624 p hg
    simpa only [d324626, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324626, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40610 p hg
    simpa only [d324626, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40626 (p : Pattern) (guard : d324627 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324620 p = 1 := by simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40611 p hg
    simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324626 p = 1 := by simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40625 p hg
    simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40627 (p : Pattern) (guard : d324628 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324621 p = 1 := by simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40612 p hg
    simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324627 p = 1 := by simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40626 p hg
    simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40628 (p : Pattern) (guard : d324629 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324626 p = 1 := by simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40625 p hg
    simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40593 p hg
    simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40629 (p : Pattern) (guard : d324630 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324627 p = 1 := by simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40626 p hg
    simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324629 p = 1 := by simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40628 p hg
    simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40630 (p : Pattern) (guard : d324631 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324628 p = 1 := by simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40627 p hg
    simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324630 p = 1 := by simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40629 p hg
    simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40631 (p : Pattern) (guard : d324632 p = 1) : d50577 p ≤ (0 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324632, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40592 p hg
    simpa only [d324632, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324631 p = 1 := by simpa only [d324632, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40630 p hg
    simpa only [d324632, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40632 (p : Pattern) (guard : d324633 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324633, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40591 p hg
    simpa only [d324633, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324632 p = 1 := by simpa only [d324633, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40631 p hg
    simpa only [d324633, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40633 (p : Pattern) (guard : d221101 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221100 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40620 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40595 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40634 (p : Pattern) (guard : d221102 p = 1) : d50570 p ≤ (0 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221101 p = 1 := by simpa only [d221102, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40633 p hg
    simpa only [d221102, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221102, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40605 p hg
    simpa only [d221102, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40635 (p : Pattern) (guard : d221103 p = 1) : d50571 p ≤ (0 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221102 p = 1 := by simpa only [d221103, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40634 p hg
    simpa only [d221103, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221103, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40607 p hg
    simpa only [d221103, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40636 (p : Pattern) (guard : d221104 p = 1) : d50572 p ≤ (0 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221104, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40594 p hg
    simpa only [d221104, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221103 p = 1 := by simpa only [d221104, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40635 p hg
    simpa only [d221104, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40637 (p : Pattern) (guard : d221105 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221104 p = 1 := by simpa only [d221105, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40636 p hg
    simpa only [d221105, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221105, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40610 p hg
    simpa only [d221105, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40638 (p : Pattern) (guard : d221106 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221105 p = 1 := by simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40637 p hg
    simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40593 p hg
    simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40639 (p : Pattern) (guard : d324634 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324629 p = 1 := by simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40628 p hg
    simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221106 p = 1 := by simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40638 p hg
    simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40640 (p : Pattern) (guard : d324635 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324630 p = 1 := by simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40629 p hg
    simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324634 p = 1 := by simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40639 p hg
    simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40641 (p : Pattern) (guard : d324636 p = 1) : d50577 p ≤ (0 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324636, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40592 p hg
    simpa only [d324636, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324635 p = 1 := by simpa only [d324636, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40640 p hg
    simpa only [d324636, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40642 (p : Pattern) (guard : d324637 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324637, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40591 p hg
    simpa only [d324637, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324636 p = 1 := by simpa only [d324637, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40641 p hg
    simpa only [d324637, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40643 (p : Pattern) (guard : d324638 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324633 p = 1 := by simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40632 p hg
    simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324637 p = 1 := by simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40642 p hg
    simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40644 (p : Pattern) (guard : d0 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40645 (p : Pattern) (guard : d324639 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324637 p = 1 := by simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40642 p hg
    simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40644 p hg
    simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40646 (p : Pattern) (guard : d324640 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324638 p = 1 := by simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40643 p hg
    simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324639 p = 1 := by simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40645 p hg
    simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40647 (p : Pattern) (guard : d324641 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324640 p = 1 := by simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40646 p hg
    simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40644 p hg
    simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40648 (p : Pattern) (guard : d0 p = 1) : d50589 p ≤ (0 : Int) + d324471 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40649 (p : Pattern) (guard : d324642 p = 1) : d50590 p ≤ (0 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324641 p = 1 := by simpa only [d324642, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40647 p hg
    simpa only [d324642, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324642, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40648 p hg
    simpa only [d324642, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40650 (p : Pattern) (guard : d324643 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324643, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d324643, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324642 p = 1 := by simpa only [d324643, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40649 p hg
    simpa only [d324643, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40651 (p : Pattern) (guard : d324644 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324639 p = 1 := by simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40645 p hg
    simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40644 p hg
    simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40652 (p : Pattern) (guard : d324645 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324644 p = 1 := by simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40651 p hg
    simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40644 p hg
    simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40653 (p : Pattern) (guard : d324646 p = 1) : d50590 p ≤ (0 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324645 p = 1 := by simpa only [d324646, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40652 p hg
    simpa only [d324646, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324646, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40648 p hg
    simpa only [d324646, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40654 (p : Pattern) (guard : d324647 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324647, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d324647, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324646 p = 1 := by simpa only [d324647, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40653 p hg
    simpa only [d324647, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40655 (p : Pattern) (guard : d324648 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324643 p = 1 := by simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40650 p hg
    simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324647 p = 1 := by simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40654 p hg
    simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40656 (p : Pattern) (guard : d324649 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324648 p = 1 := by simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40655 p hg
    simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40657 (p : Pattern) (guard : d324650 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324649 p = 1 := by simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40656 p hg
    simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40658 (p : Pattern) (guard : d324651 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324650 p = 1 := by simpa only [d324651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40657 p hg
    simpa only [d324651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40659 (p : Pattern) (guard : d324652 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324647 p = 1 := by simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40654 p hg
    simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40660 (p : Pattern) (guard : d324653 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324652 p = 1 := by simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40659 p hg
    simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40661 (p : Pattern) (guard : d324654 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324653 p = 1 := by simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40660 p hg
    simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40662 (p : Pattern) (guard : d324655 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324654 p = 1 := by simpa only [d324655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40661 p hg
    simpa only [d324655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40663 (p : Pattern) (guard : d324656 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324651 p = 1 := by simpa only [d324656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40658 p hg
    simpa only [d324656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324655 p = 1 := by simpa only [d324656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40662 p hg
    simpa only [d324656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40664 (p : Pattern) (guard : d324657 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324656 p = 1 := by simpa only [d324657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40663 p hg
    simpa only [d324657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40665 (p : Pattern) (guard : d324658 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324657 p = 1 := by simpa only [d324658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40664 p hg
    simpa only [d324658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40666 (p : Pattern) (guard : d324659 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324658 p = 1 := by simpa only [d324659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40665 p hg
    simpa only [d324659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40667 (p : Pattern) (guard : d324660 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324659 p = 1 := by simpa only [d324660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40666 p hg
    simpa only [d324660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40668 (p : Pattern) (guard : d324661 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324660 p = 1 := by simpa only [d324661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40667 p hg
    simpa only [d324661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40669 (p : Pattern) (guard : d324664 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324650 p = 1 := by simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40657 p hg
    simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40670 (p : Pattern) (guard : d324665 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324654 p = 1 := by simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40661 p hg
    simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40671 (p : Pattern) (guard : d324666 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324664 p = 1 := by simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40669 p hg
    simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324665 p = 1 := by simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40670 p hg
    simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40672 (p : Pattern) (guard : d324667 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324666 p = 1 := by simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40673 (p : Pattern) (guard : d324668 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324667 p = 1 := by simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40672 p hg
    simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40674 (p : Pattern) (guard : d324669 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324668 p = 1 := by simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40673 p hg
    simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40675 (p : Pattern) (guard : d324670 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324669 p = 1 := by simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40674 p hg
    simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40676 (p : Pattern) (guard : d324671 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d324660 p = 1 := by simpa only [d324671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40667 p hg
    simpa only [d324671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324670 p = 1 := by simpa only [d324671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40675 p hg
    simpa only [d324671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40677 (p : Pattern) (guard : d324672 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d324661 p = 1 := by simpa only [d324672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40668 p hg
    simpa only [d324672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324671 p = 1 := by simpa only [d324672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40676 p hg
    simpa only [d324672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40678 (p : Pattern) (guard : d324673 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 69 with
  | false =>
    have hg : d324672 p = 1 := by simpa only [d324673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40677 p hg
    simpa only [d324673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40679 (p : Pattern) (guard : d325179 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 51 with
  | false =>
    have hg : d324673 p = 1 := by simpa only [d325179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40678 p hg
    simpa only [d325179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d325179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40680 (p : Pattern) (guard : d325180 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d325180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325179 p = 1 := by simpa only [d325180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40679 p hg
    simpa only [d325180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40681 (p : Pattern) (guard : d0 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40682 (p : Pattern) (guard : d0 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40683 (p : Pattern) (guard : d0 p = 1) : d50671 p ≤ (0 : Int) + d324514 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40684 (p : Pattern) (guard : d0 p = 1) : d50631 p ≤ (0 : Int) + d324493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40685 (p : Pattern) (guard : d0 p = 1) : d50653 p ≤ (0 : Int) + d324499 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40686 (p : Pattern) (guard : d0 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40687 (p : Pattern) (guard : d0 p = 1) : d50656 p ≤ (0 : Int) + d324502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40688 (p : Pattern) (guard : d0 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40689 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (0 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40690 (p : Pattern) (guard : d32155 p = 1) : d49565 p ≤ (0 : Int) + d49565 p := by
  omega
theorem compare40691 (p : Pattern) (guard : d324612 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324612, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d324612, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d324612, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40690 p hg
    simpa only [d324612, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40692 (p : Pattern) (guard : d0 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40693 (p : Pattern) (guard : d324613 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d324612 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40691 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40694 (p : Pattern) (guard : d324614 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d324613 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40693 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40695 (p : Pattern) (guard : d0 p = 1) : d49566 p ≤ (0 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40696 (p : Pattern) (guard : d324615 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 182 with
  | false =>
    have hg : d324614 p = 1 := by simpa only [d324615, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40694 p hg
    simpa only [d324615, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324615, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40695 p hg
    simpa only [d324615, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40697 (p : Pattern) (guard : d324616 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40688 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324615 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40696 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40698 (p : Pattern) (guard : d0 p = 1) : d50530 p ≤ (0 : Int) + d49328 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40699 (p : Pattern) (guard : d324617 p = 1) : d50657 p ≤ (0 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324616 p = 1 := by simpa only [d324617, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40697 p hg
    simpa only [d324617, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324617, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d324617, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40700 (p : Pattern) (guard : d324618 p = 1) : d50658 p ≤ (0 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324617 p = 1 := by simpa only [d324618, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40699 p hg
    simpa only [d324618, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324618, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d324618, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40701 (p : Pattern) (guard : d324619 p = 1) : d50659 p ≤ (0 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324619, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40687 p hg
    simpa only [d324619, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324618 p = 1 := by simpa only [d324619, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40700 p hg
    simpa only [d324619, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40702 (p : Pattern) (guard : d0 p = 1) : d50662 p ≤ (0 : Int) + d324491 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40703 (p : Pattern) (guard : d324620 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324619 p = 1 := by simpa only [d324620, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40701 p hg
    simpa only [d324620, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324620, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40702 p hg
    simpa only [d324620, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40704 (p : Pattern) (guard : d324621 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40686 p hg
    simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324620 p = 1 := by simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40703 p hg
    simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40705 (p : Pattern) (guard : d1115 p = 1) : d49565 p ≤ (0 : Int) + d49565 p := by
  omega
theorem compare40706 (p : Pattern) (guard : d221076 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221076, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d221076, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d221076, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40705 p hg
    simpa only [d221076, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40707 (p : Pattern) (guard : d221096 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221076 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40706 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40708 (p : Pattern) (guard : d19 p = 1) : d49565 p ≤ (0 : Int) + d49565 p := by
  omega
theorem compare40709 (p : Pattern) (guard : d221097 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221097, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d221097, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d221097, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40708 p hg
    simpa only [d221097, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40710 (p : Pattern) (guard : d221098 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221097 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40709 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40711 (p : Pattern) (guard : d221099 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221096 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40707 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221098 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40710 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40712 (p : Pattern) (guard : d221100 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221099 p = 1 := by simpa only [d221100, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40711 p hg
    simpa only [d221100, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221100, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40695 p hg
    simpa only [d221100, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40713 (p : Pattern) (guard : d324622 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40696 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221100 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40712 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40714 (p : Pattern) (guard : d324623 p = 1) : d50657 p ≤ (0 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324622 p = 1 := by simpa only [d324623, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40713 p hg
    simpa only [d324623, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324623, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d324623, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40715 (p : Pattern) (guard : d324624 p = 1) : d50658 p ≤ (0 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324623 p = 1 := by simpa only [d324624, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40714 p hg
    simpa only [d324624, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324624, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d324624, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40716 (p : Pattern) (guard : d324625 p = 1) : d50659 p ≤ (0 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324625, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40687 p hg
    simpa only [d324625, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324624 p = 1 := by simpa only [d324625, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40715 p hg
    simpa only [d324625, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40717 (p : Pattern) (guard : d324626 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324625 p = 1 := by simpa only [d324626, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40716 p hg
    simpa only [d324626, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324626, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40702 p hg
    simpa only [d324626, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40718 (p : Pattern) (guard : d324627 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324620 p = 1 := by simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40703 p hg
    simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324626 p = 1 := by simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40717 p hg
    simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40719 (p : Pattern) (guard : d324628 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324621 p = 1 := by simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40704 p hg
    simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324627 p = 1 := by simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40718 p hg
    simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40720 (p : Pattern) (guard : d324629 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324626 p = 1 := by simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40717 p hg
    simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40686 p hg
    simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40721 (p : Pattern) (guard : d324630 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324627 p = 1 := by simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40718 p hg
    simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324629 p = 1 := by simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40720 p hg
    simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40722 (p : Pattern) (guard : d324631 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324628 p = 1 := by simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40719 p hg
    simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324630 p = 1 := by simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40721 p hg
    simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40723 (p : Pattern) (guard : d324632 p = 1) : d50664 p ≤ (0 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324632, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40685 p hg
    simpa only [d324632, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324631 p = 1 := by simpa only [d324632, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40722 p hg
    simpa only [d324632, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40724 (p : Pattern) (guard : d324633 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324633, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40684 p hg
    simpa only [d324633, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324632 p = 1 := by simpa only [d324633, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40723 p hg
    simpa only [d324633, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40725 (p : Pattern) (guard : d221101 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221100 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40712 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40688 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40726 (p : Pattern) (guard : d221102 p = 1) : d50657 p ≤ (0 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221101 p = 1 := by simpa only [d221102, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40725 p hg
    simpa only [d221102, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221102, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d221102, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40727 (p : Pattern) (guard : d221103 p = 1) : d50658 p ≤ (0 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221102 p = 1 := by simpa only [d221103, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40726 p hg
    simpa only [d221103, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221103, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d221103, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40728 (p : Pattern) (guard : d221104 p = 1) : d50659 p ≤ (0 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221104, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40687 p hg
    simpa only [d221104, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221103 p = 1 := by simpa only [d221104, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40727 p hg
    simpa only [d221104, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40729 (p : Pattern) (guard : d221105 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221104 p = 1 := by simpa only [d221105, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40728 p hg
    simpa only [d221105, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221105, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40702 p hg
    simpa only [d221105, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40730 (p : Pattern) (guard : d221106 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221105 p = 1 := by simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40729 p hg
    simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40686 p hg
    simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40731 (p : Pattern) (guard : d324634 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324629 p = 1 := by simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40720 p hg
    simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221106 p = 1 := by simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40730 p hg
    simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40732 (p : Pattern) (guard : d324635 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324630 p = 1 := by simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40721 p hg
    simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324634 p = 1 := by simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40731 p hg
    simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40733 (p : Pattern) (guard : d324636 p = 1) : d50664 p ≤ (0 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324636, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40685 p hg
    simpa only [d324636, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324635 p = 1 := by simpa only [d324636, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40732 p hg
    simpa only [d324636, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40734 (p : Pattern) (guard : d324637 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324637, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40684 p hg
    simpa only [d324637, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324636 p = 1 := by simpa only [d324637, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40733 p hg
    simpa only [d324637, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40735 (p : Pattern) (guard : d324638 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324633 p = 1 := by simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40724 p hg
    simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324637 p = 1 := by simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40734 p hg
    simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40736 (p : Pattern) (guard : d0 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40737 (p : Pattern) (guard : d324639 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324637 p = 1 := by simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40734 p hg
    simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40738 (p : Pattern) (guard : d324640 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324638 p = 1 := by simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40735 p hg
    simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324639 p = 1 := by simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40737 p hg
    simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40739 (p : Pattern) (guard : d324641 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324640 p = 1 := by simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40738 p hg
    simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40740 (p : Pattern) (guard : d0 p = 1) : d50672 p ≤ (0 : Int) + d324515 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40741 (p : Pattern) (guard : d324642 p = 1) : d50673 p ≤ (0 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324641 p = 1 := by simpa only [d324642, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40739 p hg
    simpa only [d324642, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324642, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40740 p hg
    simpa only [d324642, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40742 (p : Pattern) (guard : d324643 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324643, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40683 p hg
    simpa only [d324643, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324642 p = 1 := by simpa only [d324643, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40741 p hg
    simpa only [d324643, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40743 (p : Pattern) (guard : d324644 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324639 p = 1 := by simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40737 p hg
    simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40744 (p : Pattern) (guard : d324645 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324644 p = 1 := by simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40743 p hg
    simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40745 (p : Pattern) (guard : d324646 p = 1) : d50673 p ≤ (0 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324645 p = 1 := by simpa only [d324646, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40744 p hg
    simpa only [d324646, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324646, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40740 p hg
    simpa only [d324646, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40746 (p : Pattern) (guard : d324647 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324647, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40683 p hg
    simpa only [d324647, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324646 p = 1 := by simpa only [d324647, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40745 p hg
    simpa only [d324647, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40747 (p : Pattern) (guard : d324648 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324643 p = 1 := by simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40742 p hg
    simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324647 p = 1 := by simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40746 p hg
    simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40748 (p : Pattern) (guard : d324649 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324648 p = 1 := by simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40747 p hg
    simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40749 (p : Pattern) (guard : d324650 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324649 p = 1 := by simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40748 p hg
    simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
