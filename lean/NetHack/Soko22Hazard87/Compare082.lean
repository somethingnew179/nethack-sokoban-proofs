import NetHack.Soko22Hazard87.Compare081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20500 (p : Pattern) (guard : d54408 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54407 p = 1 := by simpa only [d54408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20499 p hg
    simpa only [d54408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20501 (p : Pattern) (guard : d54409 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54408 p = 1 := by simpa only [d54409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20500 p hg
    simpa only [d54409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20502 (p : Pattern) (guard : d138 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20503 (p : Pattern) (guard : d139 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20502 p hg
    simpa only [d139, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d139, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20504 (p : Pattern) (guard : d140 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20503 p hg
    simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20505 (p : Pattern) (guard : d141 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d141, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20504 p hg
    simpa only [d141, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20506 (p : Pattern) (guard : d142 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20505 p hg
    simpa only [d142, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d142, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20507 (p : Pattern) (guard : d143 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20506 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20401 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20508 (p : Pattern) (guard : d144 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20507 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20403 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20509 (p : Pattern) (guard : d145 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20508 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20404 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20510 (p : Pattern) (guard : d146 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d146, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20509 p hg
    simpa only [d146, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20511 (p : Pattern) (guard : d147 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d147, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d147, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20512 (p : Pattern) (guard : d148 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20511 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20407 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20513 (p : Pattern) (guard : d149 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20512 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20409 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20514 (p : Pattern) (guard : d150 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20513 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20515 (p : Pattern) (guard : d151 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d151, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d151, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20516 (p : Pattern) (guard : d152 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d152, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20515 p hg
    simpa only [d152, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20517 (p : Pattern) (guard : d153 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20516 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20414 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20518 (p : Pattern) (guard : d154 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20517 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20519 (p : Pattern) (guard : d155 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20518 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20520 (p : Pattern) (guard : d156 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20519 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20521 (p : Pattern) (guard : d157 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20520 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20418 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20522 (p : Pattern) (guard : d280 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20521 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20523 (p : Pattern) (guard : d281 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20522 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20524 (p : Pattern) (guard : d282 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20525 (p : Pattern) (guard : d283 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20524 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20526 (p : Pattern) (guard : d284 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d283 p = 1 := by simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20525 p hg
    simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20527 (p : Pattern) (guard : d147 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d147, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d147, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20528 (p : Pattern) (guard : d148 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20527 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20427 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20529 (p : Pattern) (guard : d149 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20528 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20429 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20530 (p : Pattern) (guard : d150 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20529 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20531 (p : Pattern) (guard : d151 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20530 p hg
    simpa only [d151, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d151, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20532 (p : Pattern) (guard : d152 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d152, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20531 p hg
    simpa only [d152, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20533 (p : Pattern) (guard : d153 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20532 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20433 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20534 (p : Pattern) (guard : d154 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20533 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20535 (p : Pattern) (guard : d155 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20534 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20536 (p : Pattern) (guard : d156 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20535 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20537 (p : Pattern) (guard : d157 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20536 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20437 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20538 (p : Pattern) (guard : d280 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20537 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20539 (p : Pattern) (guard : d281 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20538 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20540 (p : Pattern) (guard : d282 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20539 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20541 (p : Pattern) (guard : d283 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20540 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20542 (p : Pattern) (guard : d203 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20519 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20543 (p : Pattern) (guard : d204 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20542 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20443 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20544 (p : Pattern) (guard : d287 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d204 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20543 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20545 (p : Pattern) (guard : d288 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d287 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20544 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20546 (p : Pattern) (guard : d289 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d288 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20545 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20547 (p : Pattern) (guard : d290 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d289 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20546 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20548 (p : Pattern) (guard : d291 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20541 p hg
    simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d290 p = 1 := by simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20547 p hg
    simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20549 (p : Pattern) (guard : d292 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d284 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20526 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d291 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20548 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20550 (p : Pattern) (guard : d293 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d292 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20549 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20551 (p : Pattern) (guard : d53653 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d293 p = 1 := by simpa only [d53653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20550 p hg
    simpa only [d53653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d53653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20552 (p : Pattern) (guard : d53654 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d53654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53653 p = 1 := by simpa only [d53654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20551 p hg
    simpa only [d53654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20553 (p : Pattern) (guard : d138 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare20554 (p : Pattern) (guard : d139 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20553 p hg
    simpa only [d139, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d139, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20555 (p : Pattern) (guard : d140 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20554 p hg
    simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20556 (p : Pattern) (guard : d141 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20555 p hg
    simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20557 (p : Pattern) (guard : d142 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20556 p hg
    simpa only [d142, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d142, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20558 (p : Pattern) (guard : d143 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20557 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20466 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20559 (p : Pattern) (guard : d144 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20558 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20468 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20560 (p : Pattern) (guard : d145 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20559 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20469 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20561 (p : Pattern) (guard : d146 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d146, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20560 p hg
    simpa only [d146, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20562 (p : Pattern) (guard : d147 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d147, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20561 p hg
    simpa only [d147, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20563 (p : Pattern) (guard : d148 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20562 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20472 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20564 (p : Pattern) (guard : d149 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20563 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20474 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20565 (p : Pattern) (guard : d150 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20564 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20566 (p : Pattern) (guard : d151 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20565 p hg
    simpa only [d151, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d151, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20567 (p : Pattern) (guard : d152 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20566 p hg
    simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20568 (p : Pattern) (guard : d153 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20567 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20479 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20569 (p : Pattern) (guard : d154 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20568 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20570 (p : Pattern) (guard : d155 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20569 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20571 (p : Pattern) (guard : d203 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20570 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20572 (p : Pattern) (guard : d204 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20571 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20483 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20573 (p : Pattern) (guard : d287 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d204 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20572 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20574 (p : Pattern) (guard : d288 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d287 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20573 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20575 (p : Pattern) (guard : d289 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d288 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20574 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20576 (p : Pattern) (guard : d290 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d289 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20577 (p : Pattern) (guard : d53655 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53655, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d53655, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d290 p = 1 := by simpa only [d53655, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20576 p hg
    simpa only [d53655, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20578 (p : Pattern) (guard : d53656 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d53656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53655 p = 1 := by simpa only [d53656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20577 p hg
    simpa only [d53656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20579 (p : Pattern) (guard : d53657 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53656 p = 1 := by simpa only [d53657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20578 p hg
    simpa only [d53657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d53657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20580 (p : Pattern) (guard : d53658 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53657 p = 1 := by simpa only [d53658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20579 p hg
    simpa only [d53658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d53658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20581 (p : Pattern) (guard : d53659 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53658 p = 1 := by simpa only [d53659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20580 p hg
    simpa only [d53659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d53659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20582 (p : Pattern) (guard : d53660 p = 1) : d48359 p ≤ (0 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53654 p = 1 := by simpa only [d53660, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20552 p hg
    simpa only [d53660, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53659 p = 1 := by simpa only [d53660, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20581 p hg
    simpa only [d53660, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20583 (p : Pattern) (guard : d54410 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d53660 p = 1 := by simpa only [d54410, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20582 p hg
    simpa only [d54410, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54410, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20495 p hg
    simpa only [d54410, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20584 (p : Pattern) (guard : d54411 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54410 p = 1 := by simpa only [d54411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20583 p hg
    simpa only [d54411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20585 (p : Pattern) (guard : d54412 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54411 p = 1 := by simpa only [d54412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20584 p hg
    simpa only [d54412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20586 (p : Pattern) (guard : d54413 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54412 p = 1 := by simpa only [d54413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20585 p hg
    simpa only [d54413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20587 (p : Pattern) (guard : d54414 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54413 p = 1 := by simpa only [d54414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20586 p hg
    simpa only [d54414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20588 (p : Pattern) (guard : d54415 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54414 p = 1 := by simpa only [d54415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20587 p hg
    simpa only [d54415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20589 (p : Pattern) (guard : d54416 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d54409 p = 1 := by simpa only [d54416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20501 p hg
    simpa only [d54416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54415 p = 1 := by simpa only [d54416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20588 p hg
    simpa only [d54416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20590 (p : Pattern) (guard : d318 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20591 (p : Pattern) (guard : d319 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20590 p hg
    simpa only [d319, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d319, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20592 (p : Pattern) (guard : d320 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20591 p hg
    simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20593 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d321, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20592 p hg
    simpa only [d321, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20594 (p : Pattern) (guard : d322 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20593 p hg
    simpa only [d322, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d322, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20595 (p : Pattern) (guard : d323 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20594 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20506 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20596 (p : Pattern) (guard : d9381 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20597 (p : Pattern) (guard : d9382 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9381 p = 1 := by simpa only [d9382, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20596 p hg
    simpa only [d9382, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9382, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d9382, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20598 (p : Pattern) (guard : d9384 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9382 p = 1 := by simpa only [d9384, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20597 p hg
    simpa only [d9384, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9384, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d9384, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20599 (p : Pattern) (guard : d12493 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12493, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d12493, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9384 p = 1 := by simpa only [d12493, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20598 p hg
    simpa only [d12493, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20600 (p : Pattern) (guard : d12494 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20599 p hg
    simpa only [d12494, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d12494, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20601 (p : Pattern) (guard : d12495 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20600 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20401 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20602 (p : Pattern) (guard : d15966 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20595 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20601 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20603 (p : Pattern) (guard : d15967 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20602 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20508 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20604 (p : Pattern) (guard : d15968 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d15968, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20603 p hg
    simpa only [d15968, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20605 (p : Pattern) (guard : d15969 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d15969, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20604 p hg
    simpa only [d15969, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20606 (p : Pattern) (guard : d15970 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20605 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20511 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20607 (p : Pattern) (guard : d475 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20511 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20608 (p : Pattern) (guard : d16035 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20606 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20607 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20609 (p : Pattern) (guard : d16036 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20608 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20610 (p : Pattern) (guard : d16037 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20609 p hg
    simpa only [d16037, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16037, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20611 (p : Pattern) (guard : d16038 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d16038, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20610 p hg
    simpa only [d16038, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20612 (p : Pattern) (guard : d480 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20607 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20613 (p : Pattern) (guard : d481 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20612 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20614 (p : Pattern) (guard : d482 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20613 p hg
    simpa only [d482, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d482, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20615 (p : Pattern) (guard : d483 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d483, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20614 p hg
    simpa only [d483, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20616 (p : Pattern) (guard : d16039 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20611 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20615 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20617 (p : Pattern) (guard : d16040 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20616 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20618 (p : Pattern) (guard : d16041 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20617 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20619 (p : Pattern) (guard : d16042 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16041 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20618 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20620 (p : Pattern) (guard : d488 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20615 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20621 (p : Pattern) (guard : d489 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20620 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20622 (p : Pattern) (guard : d490 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20621 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20623 (p : Pattern) (guard : d491 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20622 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20624 (p : Pattern) (guard : d16043 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16042 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20619 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20623 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20625 (p : Pattern) (guard : d16044 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16043 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20624 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20626 (p : Pattern) (guard : d16045 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16044 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20625 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20627 (p : Pattern) (guard : d16046 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16045 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20626 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20628 (p : Pattern) (guard : d16047 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16046 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20627 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20629 (p : Pattern) (guard : d16048 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16047 p = 1 := by simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20628 p hg
    simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20630 (p : Pattern) (guard : d15969 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d15969, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20604 p hg
    simpa only [d15969, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20631 (p : Pattern) (guard : d15970 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20630 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20527 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20632 (p : Pattern) (guard : d475 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20527 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20633 (p : Pattern) (guard : d16035 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20631 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20632 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20634 (p : Pattern) (guard : d16036 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20633 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20635 (p : Pattern) (guard : d16037 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20634 p hg
    simpa only [d16037, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16037, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20636 (p : Pattern) (guard : d16038 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d16038, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20635 p hg
    simpa only [d16038, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20637 (p : Pattern) (guard : d480 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20632 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20638 (p : Pattern) (guard : d481 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20637 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20639 (p : Pattern) (guard : d482 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20638 p hg
    simpa only [d482, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d482, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20640 (p : Pattern) (guard : d483 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d483, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20639 p hg
    simpa only [d483, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20641 (p : Pattern) (guard : d16039 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20636 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20640 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20642 (p : Pattern) (guard : d16040 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20641 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20643 (p : Pattern) (guard : d16041 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20642 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20644 (p : Pattern) (guard : d16042 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16041 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20643 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20645 (p : Pattern) (guard : d488 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20640 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20646 (p : Pattern) (guard : d489 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20645 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20647 (p : Pattern) (guard : d490 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20646 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20648 (p : Pattern) (guard : d491 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20647 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20649 (p : Pattern) (guard : d16043 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16042 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20644 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20648 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20650 (p : Pattern) (guard : d16044 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16043 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20649 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20651 (p : Pattern) (guard : d16045 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16044 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20650 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20652 (p : Pattern) (guard : d16046 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16045 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20651 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20653 (p : Pattern) (guard : d16047 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16046 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20652 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20654 (p : Pattern) (guard : d16051 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16041 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20618 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20655 (p : Pattern) (guard : d501 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20622 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20656 (p : Pattern) (guard : d16052 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16051 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20654 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20655 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20657 (p : Pattern) (guard : d16053 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16052 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20656 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20658 (p : Pattern) (guard : d16054 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16053 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20657 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20659 (p : Pattern) (guard : d16055 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16054 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20658 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20660 (p : Pattern) (guard : d16056 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16055 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20659 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20661 (p : Pattern) (guard : d16057 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16047 p = 1 := by simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20653 p hg
    simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16056 p = 1 := by simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20660 p hg
    simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20662 (p : Pattern) (guard : d16058 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16048 p = 1 := by simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20629 p hg
    simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16057 p = 1 := by simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20661 p hg
    simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20663 (p : Pattern) (guard : d16059 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16058 p = 1 := by simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20662 p hg
    simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20664 (p : Pattern) (guard : d171076 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16059 p = 1 := by simpa only [d171076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20663 p hg
    simpa only [d171076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20665 (p : Pattern) (guard : d171077 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171076 p = 1 := by simpa only [d171077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20664 p hg
    simpa only [d171077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20666 (p : Pattern) (guard : d318 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare20667 (p : Pattern) (guard : d319 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20666 p hg
    simpa only [d319, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d319, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20668 (p : Pattern) (guard : d320 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20667 p hg
    simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20669 (p : Pattern) (guard : d321 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20668 p hg
    simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20670 (p : Pattern) (guard : d322 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20669 p hg
    simpa only [d322, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d322, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20671 (p : Pattern) (guard : d323 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20670 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20557 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20672 (p : Pattern) (guard : d9381 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare20673 (p : Pattern) (guard : d9382 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9381 p = 1 := by simpa only [d9382, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20672 p hg
    simpa only [d9382, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9382, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d9382, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20674 (p : Pattern) (guard : d9384 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9382 p = 1 := by simpa only [d9384, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20673 p hg
    simpa only [d9384, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9384, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d9384, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20675 (p : Pattern) (guard : d12493 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12493, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d12493, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9384 p = 1 := by simpa only [d12493, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20674 p hg
    simpa only [d12493, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20676 (p : Pattern) (guard : d12494 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20675 p hg
    simpa only [d12494, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d12494, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20677 (p : Pattern) (guard : d12495 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20676 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20466 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20678 (p : Pattern) (guard : d15966 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20671 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20677 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20679 (p : Pattern) (guard : d15967 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20678 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20559 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20680 (p : Pattern) (guard : d15968 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d15968, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20679 p hg
    simpa only [d15968, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20681 (p : Pattern) (guard : d15969 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d15969, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20680 p hg
    simpa only [d15969, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20682 (p : Pattern) (guard : d15970 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20681 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20562 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20683 (p : Pattern) (guard : d475 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20562 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20684 (p : Pattern) (guard : d16035 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20682 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20683 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20685 (p : Pattern) (guard : d16036 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20684 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20686 (p : Pattern) (guard : d16037 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20685 p hg
    simpa only [d16037, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d16037, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20687 (p : Pattern) (guard : d16038 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20686 p hg
    simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20688 (p : Pattern) (guard : d480 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20683 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20689 (p : Pattern) (guard : d481 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20688 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20690 (p : Pattern) (guard : d482 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20689 p hg
    simpa only [d482, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d482, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20691 (p : Pattern) (guard : d483 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20690 p hg
    simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20692 (p : Pattern) (guard : d16039 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20687 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20691 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20693 (p : Pattern) (guard : d16040 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20692 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20694 (p : Pattern) (guard : d16041 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20693 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20695 (p : Pattern) (guard : d16051 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16041 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20694 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20696 (p : Pattern) (guard : d488 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20691 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20697 (p : Pattern) (guard : d489 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20696 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20698 (p : Pattern) (guard : d490 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20697 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20699 (p : Pattern) (guard : d501 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20698 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20700 (p : Pattern) (guard : d16052 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16051 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20695 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20699 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20701 (p : Pattern) (guard : d16053 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16052 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20700 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20702 (p : Pattern) (guard : d16054 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16053 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20701 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20703 (p : Pattern) (guard : d16055 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16054 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20702 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20704 (p : Pattern) (guard : d16056 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16055 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20703 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20705 (p : Pattern) (guard : d171078 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171078, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d171078, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16056 p = 1 := by simpa only [d171078, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20704 p hg
    simpa only [d171078, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20706 (p : Pattern) (guard : d171079 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171078 p = 1 := by simpa only [d171079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20705 p hg
    simpa only [d171079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20707 (p : Pattern) (guard : d171080 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171079 p = 1 := by simpa only [d171080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20706 p hg
    simpa only [d171080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20708 (p : Pattern) (guard : d171081 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171080 p = 1 := by simpa only [d171081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20707 p hg
    simpa only [d171081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20709 (p : Pattern) (guard : d171082 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171081 p = 1 := by simpa only [d171082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20708 p hg
    simpa only [d171082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20710 (p : Pattern) (guard : d171083 p = 1) : d48359 p ≤ (0 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171077 p = 1 := by simpa only [d171083, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20665 p hg
    simpa only [d171083, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171082 p = 1 := by simpa only [d171083, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20709 p hg
    simpa only [d171083, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20711 (p : Pattern) (guard : d175663 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171083 p = 1 := by simpa only [d175663, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20710 p hg
    simpa only [d175663, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175663, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20495 p hg
    simpa only [d175663, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20712 (p : Pattern) (guard : d175664 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175663 p = 1 := by simpa only [d175664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20711 p hg
    simpa only [d175664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20713 (p : Pattern) (guard : d175665 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175664 p = 1 := by simpa only [d175665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20712 p hg
    simpa only [d175665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20714 (p : Pattern) (guard : d175666 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175665 p = 1 := by simpa only [d175666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20713 p hg
    simpa only [d175666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20715 (p : Pattern) (guard : d175667 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175666 p = 1 := by simpa only [d175667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20714 p hg
    simpa only [d175667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20716 (p : Pattern) (guard : d175668 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175667 p = 1 := by simpa only [d175668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20715 p hg
    simpa only [d175668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20717 (p : Pattern) (guard : d175669 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175668 p = 1 := by simpa only [d175669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20716 p hg
    simpa only [d175669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20718 (p : Pattern) (guard : d175670 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d54416 p = 1 := by simpa only [d175670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20589 p hg
    simpa only [d175670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175669 p = 1 := by simpa only [d175670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20717 p hg
    simpa only [d175670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20719 (p : Pattern) (guard : d542 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20720 (p : Pattern) (guard : d543 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20719 p hg
    simpa only [d543, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d543, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20721 (p : Pattern) (guard : d544 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20720 p hg
    simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20722 (p : Pattern) (guard : d545 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d545, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20721 p hg
    simpa only [d545, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20723 (p : Pattern) (guard : d546 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20722 p hg
    simpa only [d546, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d546, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20724 (p : Pattern) (guard : d9457 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20725 (p : Pattern) (guard : d9458 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9457 p = 1 := by simpa only [d9458, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20724 p hg
    simpa only [d9458, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9458, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d9458, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20726 (p : Pattern) (guard : d9460 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9458 p = 1 := by simpa only [d9460, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20725 p hg
    simpa only [d9460, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9460, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d9460, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20727 (p : Pattern) (guard : d16073 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16073, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d16073, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9460 p = 1 := by simpa only [d16073, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20726 p hg
    simpa only [d16073, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20728 (p : Pattern) (guard : d16074 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20727 p hg
    simpa only [d16074, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d16074, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20729 (p : Pattern) (guard : d16075 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20723 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20728 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20730 (p : Pattern) (guard : d9467 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20731 (p : Pattern) (guard : d9468 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9467 p = 1 := by simpa only [d9468, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20730 p hg
    simpa only [d9468, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9468, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d9468, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20732 (p : Pattern) (guard : d9470 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9468 p = 1 := by simpa only [d9470, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20731 p hg
    simpa only [d9470, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9470, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d9470, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20733 (p : Pattern) (guard : d12748 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12748, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d12748, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9470 p = 1 := by simpa only [d12748, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20732 p hg
    simpa only [d12748, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20734 (p : Pattern) (guard : d12749 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20733 p hg
    simpa only [d12749, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d12749, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20735 (p : Pattern) (guard : d750 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20736 (p : Pattern) (guard : d751 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20735 p hg
    simpa only [d751, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d751, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20737 (p : Pattern) (guard : d752 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20736 p hg
    simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20738 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d753, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20737 p hg
    simpa only [d753, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20739 (p : Pattern) (guard : d754 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20738 p hg
    simpa only [d754, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d754, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20740 (p : Pattern) (guard : d12750 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20734 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20739 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20741 (p : Pattern) (guard : d16227 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20729 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20740 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20742 (p : Pattern) (guard : d755 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20594 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20739 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20743 (p : Pattern) (guard : d757 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20739 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20744 (p : Pattern) (guard : d758 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20742 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20743 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20745 (p : Pattern) (guard : d16228 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20741 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20744 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20746 (p : Pattern) (guard : d16229 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d16229, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20745 p hg
    simpa only [d16229, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20747 (p : Pattern) (guard : d16230 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d16230, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20746 p hg
    simpa only [d16230, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20748 (p : Pattern) (guard : d762 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20743 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20749 (p : Pattern) (guard : d763 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20744 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20748 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
