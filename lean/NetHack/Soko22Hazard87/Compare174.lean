import NetHack.Soko22Hazard87.Compare173
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43500 (p : Pattern) (guard : d366318 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366317 p = 1 := by simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43499 p hg
    simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43501 (p : Pattern) (guard : d366319 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366318 p = 1 := by simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43500 p hg
    simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43502 (p : Pattern) (guard : d366320 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366319 p = 1 := by simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43501 p hg
    simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43503 (p : Pattern) (guard : d366324 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366314 p = 1 := by simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43474 p hg
    simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43504 (p : Pattern) (guard : d343107 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d343096 p = 1 := by simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43478 p hg
    simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43505 (p : Pattern) (guard : d366325 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366324 p = 1 := by simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43503 p hg
    simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343107 p = 1 := by simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43504 p hg
    simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43506 (p : Pattern) (guard : d366326 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366325 p = 1 := by simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43505 p hg
    simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43507 (p : Pattern) (guard : d366327 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366326 p = 1 := by simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43506 p hg
    simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43508 (p : Pattern) (guard : d366328 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366327 p = 1 := by simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43507 p hg
    simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43509 (p : Pattern) (guard : d366329 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366328 p = 1 := by simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43508 p hg
    simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43510 (p : Pattern) (guard : d366330 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366320 p = 1 := by simpa only [d366330, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43502 p hg
    simpa only [d366330, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366329 p = 1 := by simpa only [d366330, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43509 p hg
    simpa only [d366330, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43511 (p : Pattern) (guard : d366331 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366321 p = 1 := by simpa only [d366331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43485 p hg
    simpa only [d366331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366330 p = 1 := by simpa only [d366331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43510 p hg
    simpa only [d366331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43512 (p : Pattern) (guard : d366332 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366331 p = 1 := by simpa only [d366332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43511 p hg
    simpa only [d366332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43513 (p : Pattern) (guard : d366333 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366323 p = 1 := by simpa only [d366333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43487 p hg
    simpa only [d366333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366332 p = 1 := by simpa only [d366333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43512 p hg
    simpa only [d366333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43514 (p : Pattern) (guard : d366334 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366313 p = 1 := by simpa only [d366334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43473 p hg
    simpa only [d366334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43515 (p : Pattern) (guard : d366335 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366334 p = 1 := by simpa only [d366335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43514 p hg
    simpa only [d366335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43516 (p : Pattern) (guard : d343119 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343095 p = 1 := by simpa only [d343119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43477 p hg
    simpa only [d343119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43517 (p : Pattern) (guard : d343120 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343119 p = 1 := by simpa only [d343120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43516 p hg
    simpa only [d343120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43518 (p : Pattern) (guard : d366336 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366335 p = 1 := by simpa only [d366336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43515 p hg
    simpa only [d366336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343120 p = 1 := by simpa only [d366336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43517 p hg
    simpa only [d366336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43519 (p : Pattern) (guard : d366337 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366336 p = 1 := by simpa only [d366337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43518 p hg
    simpa only [d366337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43520 (p : Pattern) (guard : d366338 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366337 p = 1 := by simpa only [d366338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43519 p hg
    simpa only [d366338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43521 (p : Pattern) (guard : d366339 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366338 p = 1 := by simpa only [d366339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43520 p hg
    simpa only [d366339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43522 (p : Pattern) (guard : d366340 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366312 p = 1 := by simpa only [d366340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43472 p hg
    simpa only [d366340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43523 (p : Pattern) (guard : d366341 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366340 p = 1 := by simpa only [d366341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43522 p hg
    simpa only [d366341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43524 (p : Pattern) (guard : d366342 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366341 p = 1 := by simpa only [d366342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43523 p hg
    simpa only [d366342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43525 (p : Pattern) (guard : d343128 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343094 p = 1 := by simpa only [d343128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43476 p hg
    simpa only [d343128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43526 (p : Pattern) (guard : d343129 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343128 p = 1 := by simpa only [d343129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43525 p hg
    simpa only [d343129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43527 (p : Pattern) (guard : d343130 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343129 p = 1 := by simpa only [d343130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43526 p hg
    simpa only [d343130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43528 (p : Pattern) (guard : d366343 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366342 p = 1 := by simpa only [d366343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43524 p hg
    simpa only [d366343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343130 p = 1 := by simpa only [d366343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43527 p hg
    simpa only [d366343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43529 (p : Pattern) (guard : d366344 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366343 p = 1 := by simpa only [d366344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43528 p hg
    simpa only [d366344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43530 (p : Pattern) (guard : d366345 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366344 p = 1 := by simpa only [d366345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43529 p hg
    simpa only [d366345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43531 (p : Pattern) (guard : d366358 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43532 (p : Pattern) (guard : d366359 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366359, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366359, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366358 p = 1 := by simpa only [d366359, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43531 p hg
    simpa only [d366359, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43533 (p : Pattern) (guard : d366360 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366359 p = 1 := by simpa only [d366360, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43532 p hg
    simpa only [d366360, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366360, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366360, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43534 (p : Pattern) (guard : d366368 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43535 (p : Pattern) (guard : d366369 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366369, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366369, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366368 p = 1 := by simpa only [d366369, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43534 p hg
    simpa only [d366369, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43536 (p : Pattern) (guard : d366370 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366369 p = 1 := by simpa only [d366370, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43535 p hg
    simpa only [d366370, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366370, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366370, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43537 (p : Pattern) (guard : d366371 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366360 p = 1 := by simpa only [d366371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43533 p hg
    simpa only [d366371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366370 p = 1 := by simpa only [d366371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43536 p hg
    simpa only [d366371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43538 (p : Pattern) (guard : d366377 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43539 (p : Pattern) (guard : d366378 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366378, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366378, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366377 p = 1 := by simpa only [d366378, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43538 p hg
    simpa only [d366378, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43540 (p : Pattern) (guard : d366379 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366378 p = 1 := by simpa only [d366379, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43539 p hg
    simpa only [d366379, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366379, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366379, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43541 (p : Pattern) (guard : d366380 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366379 p = 1 := by simpa only [d366380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43540 p hg
    simpa only [d366380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342965 p = 1 := by simpa only [d366380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43267 p hg
    simpa only [d366380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43542 (p : Pattern) (guard : d366381 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366371 p = 1 := by simpa only [d366381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43537 p hg
    simpa only [d366381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366380 p = 1 := by simpa only [d366381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43541 p hg
    simpa only [d366381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43543 (p : Pattern) (guard : d366382 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366381 p = 1 := by simpa only [d366382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43542 p hg
    simpa only [d366382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366233 p = 1 := by simpa only [d366382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43269 p hg
    simpa only [d366382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43544 (p : Pattern) (guard : d366383 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366383, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366383, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366382 p = 1 := by simpa only [d366383, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43543 p hg
    simpa only [d366383, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43545 (p : Pattern) (guard : d366384 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366384, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366384, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366383 p = 1 := by simpa only [d366384, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43544 p hg
    simpa only [d366384, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43546 (p : Pattern) (guard : d343174 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342966 p = 1 := by simpa only [d343174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43268 p hg
    simpa only [d343174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342718 p = 1 := by simpa only [d343174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42907 p hg
    simpa only [d343174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43547 (p : Pattern) (guard : d366385 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366233 p = 1 := by simpa only [d366385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43269 p hg
    simpa only [d366385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343174 p = 1 := by simpa only [d366385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43546 p hg
    simpa only [d366385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43548 (p : Pattern) (guard : d366386 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366386, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366386, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366385 p = 1 := by simpa only [d366386, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43547 p hg
    simpa only [d366386, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43549 (p : Pattern) (guard : d366387 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366387, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366387, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366386 p = 1 := by simpa only [d366387, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43548 p hg
    simpa only [d366387, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43550 (p : Pattern) (guard : d366388 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366384 p = 1 := by simpa only [d366388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43545 p hg
    simpa only [d366388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366387 p = 1 := by simpa only [d366388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43549 p hg
    simpa only [d366388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43551 (p : Pattern) (guard : d366389 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366388 p = 1 := by simpa only [d366389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43550 p hg
    simpa only [d366389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366237 p = 1 := by simpa only [d366389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43273 p hg
    simpa only [d366389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43552 (p : Pattern) (guard : d366390 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366389 p = 1 := by simpa only [d366390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43551 p hg
    simpa only [d366390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43553 (p : Pattern) (guard : d366391 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366390 p = 1 := by simpa only [d366391, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43552 p hg
    simpa only [d366391, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366391, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d366391, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43554 (p : Pattern) (guard : d366392 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366392, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366392, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366391 p = 1 := by simpa only [d366392, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43553 p hg
    simpa only [d366392, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43555 (p : Pattern) (guard : d366393 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366392 p = 1 := by simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43554 p hg
    simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366311 p = 1 := by simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43467 p hg
    simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43556 (p : Pattern) (guard : d366394 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366393 p = 1 := by simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43555 p hg
    simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43557 (p : Pattern) (guard : d366395 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366394 p = 1 := by simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43556 p hg
    simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43558 (p : Pattern) (guard : d366396 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366395 p = 1 := by simpa only [d366396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43557 p hg
    simpa only [d366396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43559 (p : Pattern) (guard : d366397 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366396 p = 1 := by simpa only [d366397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43558 p hg
    simpa only [d366397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366315 p = 1 := by simpa only [d366397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43475 p hg
    simpa only [d366397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43560 (p : Pattern) (guard : d366398 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366397 p = 1 := by simpa only [d366398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43559 p hg
    simpa only [d366398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43561 (p : Pattern) (guard : d366399 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366311 p = 1 := by simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43467 p hg
    simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43562 (p : Pattern) (guard : d366400 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366399 p = 1 := by simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43561 p hg
    simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43563 (p : Pattern) (guard : d366401 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366400 p = 1 := by simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43562 p hg
    simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43564 (p : Pattern) (guard : d366402 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366401 p = 1 := by simpa only [d366402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43563 p hg
    simpa only [d366402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43565 (p : Pattern) (guard : d366403 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366402 p = 1 := by simpa only [d366403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43564 p hg
    simpa only [d366403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43566 (p : Pattern) (guard : d366404 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366403 p = 1 := by simpa only [d366404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43565 p hg
    simpa only [d366404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43567 (p : Pattern) (guard : d366405 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366398 p = 1 := by simpa only [d366405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43560 p hg
    simpa only [d366405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366404 p = 1 := by simpa only [d366405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43566 p hg
    simpa only [d366405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43568 (p : Pattern) (guard : d366406 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d366345 p = 1 := by simpa only [d366406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43530 p hg
    simpa only [d366406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366405 p = 1 := by simpa only [d366406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43567 p hg
    simpa only [d366406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43569 (p : Pattern) (guard : d366407 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d366339 p = 1 := by simpa only [d366407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43521 p hg
    simpa only [d366407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366406 p = 1 := by simpa only [d366407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43568 p hg
    simpa only [d366407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43570 (p : Pattern) (guard : d366408 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366408, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366408, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366407 p = 1 := by simpa only [d366408, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43569 p hg
    simpa only [d366408, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43571 (p : Pattern) (guard : d366334 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366313 p = 1 := by simpa only [d366334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43491 p hg
    simpa only [d366334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43572 (p : Pattern) (guard : d366335 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366334 p = 1 := by simpa only [d366335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43571 p hg
    simpa only [d366335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43573 (p : Pattern) (guard : d343119 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343095 p = 1 := by simpa only [d343119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43495 p hg
    simpa only [d343119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43574 (p : Pattern) (guard : d343120 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343119 p = 1 := by simpa only [d343120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43573 p hg
    simpa only [d343120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43575 (p : Pattern) (guard : d366336 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366335 p = 1 := by simpa only [d366336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43572 p hg
    simpa only [d366336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343120 p = 1 := by simpa only [d366336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43574 p hg
    simpa only [d366336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43576 (p : Pattern) (guard : d366337 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366336 p = 1 := by simpa only [d366337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43575 p hg
    simpa only [d366337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43577 (p : Pattern) (guard : d366338 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366337 p = 1 := by simpa only [d366338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43576 p hg
    simpa only [d366338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43578 (p : Pattern) (guard : d366339 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366338 p = 1 := by simpa only [d366339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43577 p hg
    simpa only [d366339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43579 (p : Pattern) (guard : d366340 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366312 p = 1 := by simpa only [d366340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43490 p hg
    simpa only [d366340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43580 (p : Pattern) (guard : d366341 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366340 p = 1 := by simpa only [d366341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43579 p hg
    simpa only [d366341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43581 (p : Pattern) (guard : d366342 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366341 p = 1 := by simpa only [d366342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43580 p hg
    simpa only [d366342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43582 (p : Pattern) (guard : d343128 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343094 p = 1 := by simpa only [d343128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43494 p hg
    simpa only [d343128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43583 (p : Pattern) (guard : d343129 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343128 p = 1 := by simpa only [d343129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43582 p hg
    simpa only [d343129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43584 (p : Pattern) (guard : d343130 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343129 p = 1 := by simpa only [d343130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43583 p hg
    simpa only [d343130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43585 (p : Pattern) (guard : d366343 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366342 p = 1 := by simpa only [d366343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43581 p hg
    simpa only [d366343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343130 p = 1 := by simpa only [d366343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43584 p hg
    simpa only [d366343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43586 (p : Pattern) (guard : d366344 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366343 p = 1 := by simpa only [d366344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43585 p hg
    simpa only [d366344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43587 (p : Pattern) (guard : d366345 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366344 p = 1 := by simpa only [d366345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43586 p hg
    simpa only [d366345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43588 (p : Pattern) (guard : d366392 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366392, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d366392, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366391 p = 1 := by simpa only [d366392, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43553 p hg
    simpa only [d366392, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43589 (p : Pattern) (guard : d366393 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366392 p = 1 := by simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43588 p hg
    simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366311 p = 1 := by simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43488 p hg
    simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43590 (p : Pattern) (guard : d366394 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366393 p = 1 := by simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43589 p hg
    simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43591 (p : Pattern) (guard : d366395 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366394 p = 1 := by simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43590 p hg
    simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43592 (p : Pattern) (guard : d366396 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366395 p = 1 := by simpa only [d366396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43591 p hg
    simpa only [d366396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43593 (p : Pattern) (guard : d366397 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366396 p = 1 := by simpa only [d366397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43592 p hg
    simpa only [d366397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366315 p = 1 := by simpa only [d366397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43493 p hg
    simpa only [d366397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43594 (p : Pattern) (guard : d366398 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366397 p = 1 := by simpa only [d366398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43593 p hg
    simpa only [d366398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43595 (p : Pattern) (guard : d366399 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366311 p = 1 := by simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43488 p hg
    simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43596 (p : Pattern) (guard : d366400 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366399 p = 1 := by simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43595 p hg
    simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43597 (p : Pattern) (guard : d366401 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366400 p = 1 := by simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43596 p hg
    simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43598 (p : Pattern) (guard : d366402 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366401 p = 1 := by simpa only [d366402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43597 p hg
    simpa only [d366402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43599 (p : Pattern) (guard : d366403 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366402 p = 1 := by simpa only [d366403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43598 p hg
    simpa only [d366403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43600 (p : Pattern) (guard : d366404 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366403 p = 1 := by simpa only [d366404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43599 p hg
    simpa only [d366404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43601 (p : Pattern) (guard : d366405 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366398 p = 1 := by simpa only [d366405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43594 p hg
    simpa only [d366405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366404 p = 1 := by simpa only [d366405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43600 p hg
    simpa only [d366405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43602 (p : Pattern) (guard : d366406 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d366345 p = 1 := by simpa only [d366406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43587 p hg
    simpa only [d366406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366405 p = 1 := by simpa only [d366406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43601 p hg
    simpa only [d366406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43603 (p : Pattern) (guard : d366407 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d366339 p = 1 := by simpa only [d366407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43578 p hg
    simpa only [d366407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366406 p = 1 := by simpa only [d366407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43602 p hg
    simpa only [d366407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43604 (p : Pattern) (guard : d366409 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366334 p = 1 := by simpa only [d366409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43514 p hg
    simpa only [d366409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43605 (p : Pattern) (guard : d343200 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d343119 p = 1 := by simpa only [d343200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43516 p hg
    simpa only [d343200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43606 (p : Pattern) (guard : d366410 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366409 p = 1 := by simpa only [d366410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43604 p hg
    simpa only [d366410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343200 p = 1 := by simpa only [d366410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43605 p hg
    simpa only [d366410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43607 (p : Pattern) (guard : d366411 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366410 p = 1 := by simpa only [d366411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43606 p hg
    simpa only [d366411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43608 (p : Pattern) (guard : d366412 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366411 p = 1 := by simpa only [d366412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43607 p hg
    simpa only [d366412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43609 (p : Pattern) (guard : d366413 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366412 p = 1 := by simpa only [d366413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43608 p hg
    simpa only [d366413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43610 (p : Pattern) (guard : d366414 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366341 p = 1 := by simpa only [d366414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43523 p hg
    simpa only [d366414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43611 (p : Pattern) (guard : d343206 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d343129 p = 1 := by simpa only [d343206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43526 p hg
    simpa only [d343206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43612 (p : Pattern) (guard : d366415 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366414 p = 1 := by simpa only [d366415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43610 p hg
    simpa only [d366415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343206 p = 1 := by simpa only [d366415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43611 p hg
    simpa only [d366415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43613 (p : Pattern) (guard : d366416 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366415 p = 1 := by simpa only [d366416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43612 p hg
    simpa only [d366416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43614 (p : Pattern) (guard : d366417 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366416 p = 1 := by simpa only [d366417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43613 p hg
    simpa only [d366417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43615 (p : Pattern) (guard : d366418 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366395 p = 1 := by simpa only [d366418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43557 p hg
    simpa only [d366418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43616 (p : Pattern) (guard : d366419 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366418 p = 1 := by simpa only [d366419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43615 p hg
    simpa only [d366419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366324 p = 1 := by simpa only [d366419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43503 p hg
    simpa only [d366419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43617 (p : Pattern) (guard : d366420 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366419 p = 1 := by simpa only [d366420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43616 p hg
    simpa only [d366420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43618 (p : Pattern) (guard : d366421 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366401 p = 1 := by simpa only [d366421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43563 p hg
    simpa only [d366421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43619 (p : Pattern) (guard : d366422 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366421 p = 1 := by simpa only [d366422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43618 p hg
    simpa only [d366422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43620 (p : Pattern) (guard : d366423 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366422 p = 1 := by simpa only [d366423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43619 p hg
    simpa only [d366423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43621 (p : Pattern) (guard : d366424 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366420 p = 1 := by simpa only [d366424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43617 p hg
    simpa only [d366424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366423 p = 1 := by simpa only [d366424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43620 p hg
    simpa only [d366424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43622 (p : Pattern) (guard : d366425 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d366417 p = 1 := by simpa only [d366425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43614 p hg
    simpa only [d366425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366424 p = 1 := by simpa only [d366425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43621 p hg
    simpa only [d366425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43623 (p : Pattern) (guard : d366426 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d366413 p = 1 := by simpa only [d366426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43609 p hg
    simpa only [d366426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366425 p = 1 := by simpa only [d366426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43622 p hg
    simpa only [d366426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43624 (p : Pattern) (guard : d366427 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366407 p = 1 := by simpa only [d366427, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43603 p hg
    simpa only [d366427, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366426 p = 1 := by simpa only [d366427, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43623 p hg
    simpa only [d366427, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43625 (p : Pattern) (guard : d366428 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366408 p = 1 := by simpa only [d366428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43570 p hg
    simpa only [d366428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366427 p = 1 := by simpa only [d366428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43624 p hg
    simpa only [d366428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43626 (p : Pattern) (guard : d343221 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d343097 p = 1 := by simpa only [d343221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43479 p hg
    simpa only [d343221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43627 (p : Pattern) (guard : d343222 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343221 p = 1 := by simpa only [d343222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43626 p hg
    simpa only [d343222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43628 (p : Pattern) (guard : d343223 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d343222 p = 1 := by simpa only [d343223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43627 p hg
    simpa only [d343223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43629 (p : Pattern) (guard : d343224 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343223 p = 1 := by simpa only [d343224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43628 p hg
    simpa only [d343224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43630 (p : Pattern) (guard : d343225 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343224 p = 1 := by simpa only [d343225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43629 p hg
    simpa only [d343225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43631 (p : Pattern) (guard : d366429 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366320 p = 1 := by simpa only [d366429, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43502 p hg
    simpa only [d366429, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343225 p = 1 := by simpa only [d366429, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43630 p hg
    simpa only [d366429, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43632 (p : Pattern) (guard : d343221 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d343097 p = 1 := by simpa only [d343221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43497 p hg
    simpa only [d343221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43633 (p : Pattern) (guard : d343222 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343221 p = 1 := by simpa only [d343222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43632 p hg
    simpa only [d343222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43634 (p : Pattern) (guard : d343223 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d343222 p = 1 := by simpa only [d343223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43633 p hg
    simpa only [d343223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43635 (p : Pattern) (guard : d343224 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343223 p = 1 := by simpa only [d343224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43634 p hg
    simpa only [d343224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43636 (p : Pattern) (guard : d343225 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343224 p = 1 := by simpa only [d343225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43635 p hg
    simpa only [d343225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43637 (p : Pattern) (guard : d343227 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d343107 p = 1 := by simpa only [d343227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43504 p hg
    simpa only [d343227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43638 (p : Pattern) (guard : d343228 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343227 p = 1 := by simpa only [d343228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43637 p hg
    simpa only [d343228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43639 (p : Pattern) (guard : d343229 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d343228 p = 1 := by simpa only [d343229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43638 p hg
    simpa only [d343229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43640 (p : Pattern) (guard : d343230 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343229 p = 1 := by simpa only [d343230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43639 p hg
    simpa only [d343230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43641 (p : Pattern) (guard : d343231 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343230 p = 1 := by simpa only [d343231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43640 p hg
    simpa only [d343231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43642 (p : Pattern) (guard : d343232 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d343225 p = 1 := by simpa only [d343232, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43636 p hg
    simpa only [d343232, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343231 p = 1 := by simpa only [d343232, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43641 p hg
    simpa only [d343232, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43643 (p : Pattern) (guard : d366430 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366429 p = 1 := by simpa only [d366430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43631 p hg
    simpa only [d366430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343232 p = 1 := by simpa only [d366430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43642 p hg
    simpa only [d366430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43644 (p : Pattern) (guard : d366431 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366428 p = 1 := by simpa only [d366431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43625 p hg
    simpa only [d366431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366430 p = 1 := by simpa only [d366431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43643 p hg
    simpa only [d366431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43645 (p : Pattern) (guard : d366432 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366431 p = 1 := by simpa only [d366432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43644 p hg
    simpa only [d366432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43646 (p : Pattern) (guard : d366433 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d366333 p = 1 := by simpa only [d366433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43513 p hg
    simpa only [d366433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366432 p = 1 := by simpa only [d366433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43645 p hg
    simpa only [d366433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43647 (p : Pattern) (guard : d366358 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare43648 (p : Pattern) (guard : d366359 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366359, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366359, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366358 p = 1 := by simpa only [d366359, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43647 p hg
    simpa only [d366359, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43649 (p : Pattern) (guard : d366360 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366359 p = 1 := by simpa only [d366360, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43648 p hg
    simpa only [d366360, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366360, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366360, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43650 (p : Pattern) (guard : d366368 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare43651 (p : Pattern) (guard : d366369 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366369, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366369, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366368 p = 1 := by simpa only [d366369, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43650 p hg
    simpa only [d366369, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43652 (p : Pattern) (guard : d366370 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366369 p = 1 := by simpa only [d366370, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43651 p hg
    simpa only [d366370, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366370, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366370, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43653 (p : Pattern) (guard : d366371 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366360 p = 1 := by simpa only [d366371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43649 p hg
    simpa only [d366371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366370 p = 1 := by simpa only [d366371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43652 p hg
    simpa only [d366371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43654 (p : Pattern) (guard : d366377 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare43655 (p : Pattern) (guard : d366378 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366378, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366378, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366377 p = 1 := by simpa only [d366378, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43654 p hg
    simpa only [d366378, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43656 (p : Pattern) (guard : d366379 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366378 p = 1 := by simpa only [d366379, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43655 p hg
    simpa only [d366379, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366379, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366379, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43657 (p : Pattern) (guard : d366380 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366379 p = 1 := by simpa only [d366380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43656 p hg
    simpa only [d366380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342965 p = 1 := by simpa only [d366380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43353 p hg
    simpa only [d366380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43658 (p : Pattern) (guard : d366381 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366371 p = 1 := by simpa only [d366381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43653 p hg
    simpa only [d366381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366380 p = 1 := by simpa only [d366381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43657 p hg
    simpa only [d366381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43659 (p : Pattern) (guard : d366382 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366381 p = 1 := by simpa only [d366382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43658 p hg
    simpa only [d366382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366233 p = 1 := by simpa only [d366382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43355 p hg
    simpa only [d366382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43660 (p : Pattern) (guard : d366383 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366383, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366383, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366382 p = 1 := by simpa only [d366383, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43659 p hg
    simpa only [d366383, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43661 (p : Pattern) (guard : d366384 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366384, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366384, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366383 p = 1 := by simpa only [d366384, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43660 p hg
    simpa only [d366384, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43662 (p : Pattern) (guard : d343174 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342966 p = 1 := by simpa only [d343174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43354 p hg
    simpa only [d343174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342718 p = 1 := by simpa only [d343174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42962 p hg
    simpa only [d343174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43663 (p : Pattern) (guard : d366385 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366233 p = 1 := by simpa only [d366385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43355 p hg
    simpa only [d366385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343174 p = 1 := by simpa only [d366385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43662 p hg
    simpa only [d366385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43664 (p : Pattern) (guard : d366386 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366386, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366386, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366385 p = 1 := by simpa only [d366386, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43663 p hg
    simpa only [d366386, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43665 (p : Pattern) (guard : d366387 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366387, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366387, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366386 p = 1 := by simpa only [d366387, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43664 p hg
    simpa only [d366387, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43666 (p : Pattern) (guard : d366388 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366384 p = 1 := by simpa only [d366388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43661 p hg
    simpa only [d366388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366387 p = 1 := by simpa only [d366388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43665 p hg
    simpa only [d366388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43667 (p : Pattern) (guard : d366389 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366388 p = 1 := by simpa only [d366389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43666 p hg
    simpa only [d366389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366237 p = 1 := by simpa only [d366389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43359 p hg
    simpa only [d366389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43668 (p : Pattern) (guard : d366390 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366389 p = 1 := by simpa only [d366390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43667 p hg
    simpa only [d366390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43669 (p : Pattern) (guard : d366391 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366390 p = 1 := by simpa only [d366391, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43668 p hg
    simpa only [d366391, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366391, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d366391, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43670 (p : Pattern) (guard : d366392 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366392, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d366392, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366391 p = 1 := by simpa only [d366392, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43669 p hg
    simpa only [d366392, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43671 (p : Pattern) (guard : d343081 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342833 p = 1 := by simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43159 p hg
    simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43672 (p : Pattern) (guard : d366308 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366237 p = 1 := by simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43359 p hg
    simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343081 p = 1 := by simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43671 p hg
    simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43673 (p : Pattern) (guard : d366309 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366308 p = 1 := by simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43672 p hg
    simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43674 (p : Pattern) (guard : d366310 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366309 p = 1 := by simpa only [d366310, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43673 p hg
    simpa only [d366310, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366310, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d366310, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43675 (p : Pattern) (guard : d366311 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366311, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d366311, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366310 p = 1 := by simpa only [d366311, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43674 p hg
    simpa only [d366311, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43676 (p : Pattern) (guard : d366393 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366392 p = 1 := by simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43670 p hg
    simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366311 p = 1 := by simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43675 p hg
    simpa only [d366393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43677 (p : Pattern) (guard : d366394 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366393 p = 1 := by simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43676 p hg
    simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43678 (p : Pattern) (guard : d366395 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366394 p = 1 := by simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43677 p hg
    simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43679 (p : Pattern) (guard : d366418 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366395 p = 1 := by simpa only [d366418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43678 p hg
    simpa only [d366418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43680 (p : Pattern) (guard : d343086 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d343081 p = 1 := by simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43671 p hg
    simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43681 (p : Pattern) (guard : d343087 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d343086 p = 1 := by simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43680 p hg
    simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43682 (p : Pattern) (guard : d343088 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d343087 p = 1 := by simpa only [d343088, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43681 p hg
    simpa only [d343088, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343088, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d343088, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43683 (p : Pattern) (guard : d343089 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343089, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d343089, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343088 p = 1 := by simpa only [d343089, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43682 p hg
    simpa only [d343089, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43684 (p : Pattern) (guard : d366312 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366311 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43675 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343089 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43683 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43685 (p : Pattern) (guard : d366313 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366312 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43684 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43686 (p : Pattern) (guard : d366314 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366313 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43685 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43687 (p : Pattern) (guard : d366324 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366314 p = 1 := by simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43686 p hg
    simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43688 (p : Pattern) (guard : d366419 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366418 p = 1 := by simpa only [d366419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43679 p hg
    simpa only [d366419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366324 p = 1 := by simpa only [d366419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43687 p hg
    simpa only [d366419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43689 (p : Pattern) (guard : d366420 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366419 p = 1 := by simpa only [d366420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43688 p hg
    simpa only [d366420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43690 (p : Pattern) (guard : d366399 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366311 p = 1 := by simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43675 p hg
    simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43691 (p : Pattern) (guard : d366400 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366399 p = 1 := by simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43690 p hg
    simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43692 (p : Pattern) (guard : d366401 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366400 p = 1 := by simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43691 p hg
    simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43693 (p : Pattern) (guard : d366421 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366401 p = 1 := by simpa only [d366421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43692 p hg
    simpa only [d366421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43694 (p : Pattern) (guard : d366422 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366421 p = 1 := by simpa only [d366422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43693 p hg
    simpa only [d366422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43695 (p : Pattern) (guard : d366423 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366422 p = 1 := by simpa only [d366423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43694 p hg
    simpa only [d366423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43696 (p : Pattern) (guard : d366424 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366420 p = 1 := by simpa only [d366424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43689 p hg
    simpa only [d366424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366423 p = 1 := by simpa only [d366424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43695 p hg
    simpa only [d366424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43697 (p : Pattern) (guard : d366434 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366424 p = 1 := by simpa only [d366434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43696 p hg
    simpa only [d366434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43698 (p : Pattern) (guard : d366435 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366434 p = 1 := by simpa only [d366435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43697 p hg
    simpa only [d366435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43699 (p : Pattern) (guard : d366436 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366436, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366436, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366435 p = 1 := by simpa only [d366436, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43698 p hg
    simpa only [d366436, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43700 (p : Pattern) (guard : d366437 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366436 p = 1 := by simpa only [d366437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43699 p hg
    simpa only [d366437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43701 (p : Pattern) (guard : d343094 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d343089 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43683 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43702 (p : Pattern) (guard : d343095 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d343094 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43701 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43703 (p : Pattern) (guard : d343096 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343095 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43702 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43704 (p : Pattern) (guard : d343107 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d343096 p = 1 := by simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43703 p hg
    simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43705 (p : Pattern) (guard : d343227 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d343107 p = 1 := by simpa only [d343227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43704 p hg
    simpa only [d343227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43706 (p : Pattern) (guard : d343228 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343227 p = 1 := by simpa only [d343228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43705 p hg
    simpa only [d343228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43707 (p : Pattern) (guard : d343229 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d343228 p = 1 := by simpa only [d343229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43706 p hg
    simpa only [d343229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43708 (p : Pattern) (guard : d343230 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343229 p = 1 := by simpa only [d343230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43707 p hg
    simpa only [d343230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43709 (p : Pattern) (guard : d343231 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343230 p = 1 := by simpa only [d343231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43708 p hg
    simpa only [d343231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43710 (p : Pattern) (guard : d343241 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343241, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343241, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343231 p = 1 := by simpa only [d343241, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43709 p hg
    simpa only [d343241, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43711 (p : Pattern) (guard : d343242 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d343242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343241 p = 1 := by simpa only [d343242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43710 p hg
    simpa only [d343242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43712 (p : Pattern) (guard : d366438 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366437 p = 1 := by simpa only [d366438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43700 p hg
    simpa only [d366438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343242 p = 1 := by simpa only [d366438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43711 p hg
    simpa only [d366438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43713 (p : Pattern) (guard : d366439 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366438 p = 1 := by simpa only [d366439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43712 p hg
    simpa only [d366439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43714 (p : Pattern) (guard : d366440 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d366439 p = 1 := by simpa only [d366440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43713 p hg
    simpa only [d366440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43715 (p : Pattern) (guard : d366441 p = 1) : d51470 p ≤ (8 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d366433 p = 1 := by simpa only [d366441, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43646 p hg
    simpa only [d366441, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366440 p = 1 := by simpa only [d366441, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43714 p hg
    simpa only [d366441, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43716 (p : Pattern) (guard : d366346 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42943 p = 1 := by simpa only [d366346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43397 p hg
    simpa only [d366346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43717 (p : Pattern) (guard : d366347 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d42940 p = 1 := by simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43394 p hg
    simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43000 p hg
    simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43718 (p : Pattern) (guard : d366348 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d366347 p = 1 := by simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43717 p hg
    simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43719 (p : Pattern) (guard : d366349 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366348 p = 1 := by simpa only [d366349, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43718 p hg
    simpa only [d366349, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366349, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d366349, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43720 (p : Pattern) (guard : d366350 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d42943 p = 1 := by simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43397 p hg
    simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366349 p = 1 := by simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43719 p hg
    simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43721 (p : Pattern) (guard : d366351 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366346 p = 1 := by simpa only [d366351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43716 p hg
    simpa only [d366351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366350 p = 1 := by simpa only [d366351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43720 p hg
    simpa only [d366351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43722 (p : Pattern) (guard : d366352 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366351 p = 1 := by simpa only [d366352, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43721 p hg
    simpa only [d366352, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366352, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366352, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43723 (p : Pattern) (guard : d366353 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366349 p = 1 := by simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43719 p hg
    simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43004 p hg
    simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43724 (p : Pattern) (guard : d366354 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366224 p = 1 := by simpa only [d366354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43398 p hg
    simpa only [d366354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366353 p = 1 := by simpa only [d366354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43723 p hg
    simpa only [d366354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43725 (p : Pattern) (guard : d366355 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366354 p = 1 := by simpa only [d366355, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43724 p hg
    simpa only [d366355, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366355, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366355, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43726 (p : Pattern) (guard : d366356 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366352 p = 1 := by simpa only [d366356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43722 p hg
    simpa only [d366356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366355 p = 1 := by simpa only [d366356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43725 p hg
    simpa only [d366356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43727 (p : Pattern) (guard : d366442 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366442, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366442, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366356 p = 1 := by simpa only [d366442, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43726 p hg
    simpa only [d366442, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43728 (p : Pattern) (guard : d366357 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare43729 (p : Pattern) (guard : d366443 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366442 p = 1 := by simpa only [d366443, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43727 p hg
    simpa only [d366443, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366357 p = 1 := by simpa only [d366443, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43728 p hg
    simpa only [d366443, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43730 (p : Pattern) (guard : d366358 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare43731 (p : Pattern) (guard : d366444 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366443 p = 1 := by simpa only [d366444, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43729 p hg
    simpa only [d366444, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366358 p = 1 := by simpa only [d366444, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43730 p hg
    simpa only [d366444, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43732 (p : Pattern) (guard : d366445 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366444 p = 1 := by simpa only [d366445, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43731 p hg
    simpa only [d366445, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366445, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366445, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43733 (p : Pattern) (guard : d1525 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43183 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43734 (p : Pattern) (guard : d32153 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43733 p hg
    simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43735 (p : Pattern) (guard : d366361 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32153 p = 1 := by simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43734 p hg
    simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43736 (p : Pattern) (guard : d366362 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366361 p = 1 := by simpa only [d366362, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43735 p hg
    simpa only [d366362, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366362, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d366362, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43737 (p : Pattern) (guard : d366363 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366362 p = 1 := by simpa only [d366363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43736 p hg
    simpa only [d366363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43004 p hg
    simpa only [d366363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43738 (p : Pattern) (guard : d366364 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366363 p = 1 := by simpa only [d366364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43737 p hg
    simpa only [d366364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43739 (p : Pattern) (guard : d366365 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366364 p = 1 := by simpa only [d366365, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43738 p hg
    simpa only [d366365, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366365, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366365, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43740 (p : Pattern) (guard : d366366 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366226 p = 1 := by simpa only [d366366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43400 p hg
    simpa only [d366366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366365 p = 1 := by simpa only [d366366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43739 p hg
    simpa only [d366366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43741 (p : Pattern) (guard : d366446 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366446, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366446, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366366 p = 1 := by simpa only [d366446, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43740 p hg
    simpa only [d366446, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43742 (p : Pattern) (guard : d366367 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare43743 (p : Pattern) (guard : d366447 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366446 p = 1 := by simpa only [d366447, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43741 p hg
    simpa only [d366447, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366367 p = 1 := by simpa only [d366447, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43742 p hg
    simpa only [d366447, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43744 (p : Pattern) (guard : d366368 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare43745 (p : Pattern) (guard : d366448 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366447 p = 1 := by simpa only [d366448, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43743 p hg
    simpa only [d366448, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366368 p = 1 := by simpa only [d366448, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43744 p hg
    simpa only [d366448, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43746 (p : Pattern) (guard : d366449 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366448 p = 1 := by simpa only [d366449, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43745 p hg
    simpa only [d366449, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366449, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366449, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43747 (p : Pattern) (guard : d366450 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366445 p = 1 := by simpa only [d366450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43732 p hg
    simpa only [d366450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366449 p = 1 := by simpa only [d366450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43746 p hg
    simpa only [d366450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43748 (p : Pattern) (guard : d366372 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d42943 p = 1 := by simpa only [d366372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43397 p hg
    simpa only [d366372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366362 p = 1 := by simpa only [d366372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43736 p hg
    simpa only [d366372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43749 (p : Pattern) (guard : d366373 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366372 p = 1 := by simpa only [d366373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43748 p hg
    simpa only [d366373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
