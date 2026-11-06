import NetHack.Soko22Hazard87.Compare149
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37500 (p : Pattern) (guard : d318072 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318071 p = 1 := by simpa only [d318072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37499 p hg
    simpa only [d318072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37501 (p : Pattern) (guard : d318073 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318072 p = 1 := by simpa only [d318073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37500 p hg
    simpa only [d318073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37502 (p : Pattern) (guard : d318074 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318049 p = 1 := by simpa only [d318074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37438 p hg
    simpa only [d318074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37503 (p : Pattern) (guard : d318075 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318074 p = 1 := by simpa only [d318075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37502 p hg
    simpa only [d318075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318015 p = 1 := by simpa only [d318075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d318075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37504 (p : Pattern) (guard : d318076 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318075 p = 1 := by simpa only [d318076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37503 p hg
    simpa only [d318076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37505 (p : Pattern) (guard : d318077 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318055 p = 1 := by simpa only [d318077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37444 p hg
    simpa only [d318077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37506 (p : Pattern) (guard : d318078 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318077 p = 1 := by simpa only [d318078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37505 p hg
    simpa only [d318078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37507 (p : Pattern) (guard : d318079 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318078 p = 1 := by simpa only [d318079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37506 p hg
    simpa only [d318079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37508 (p : Pattern) (guard : d318080 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318076 p = 1 := by simpa only [d318080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37504 p hg
    simpa only [d318080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318079 p = 1 := by simpa only [d318080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37507 p hg
    simpa only [d318080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37509 (p : Pattern) (guard : d318081 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d318073 p = 1 := by simpa only [d318081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37501 p hg
    simpa only [d318081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318080 p = 1 := by simpa only [d318081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37508 p hg
    simpa only [d318081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37510 (p : Pattern) (guard : d318082 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d318068 p = 1 := by simpa only [d318082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37496 p hg
    simpa only [d318082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318081 p = 1 := by simpa only [d318082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37509 p hg
    simpa only [d318082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37511 (p : Pattern) (guard : d318083 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d318061 p = 1 := by simpa only [d318083, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37490 p hg
    simpa only [d318083, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318082 p = 1 := by simpa only [d318083, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37510 p hg
    simpa only [d318083, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37512 (p : Pattern) (guard : d318084 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d318062 p = 1 := by simpa only [d318084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37451 p hg
    simpa only [d318084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318083 p = 1 := by simpa only [d318084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37511 p hg
    simpa only [d318084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37513 (p : Pattern) (guard : d318085 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318006 p = 1 := by simpa only [d318085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37363 p hg
    simpa only [d318085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37514 (p : Pattern) (guard : d318086 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318085 p = 1 := by simpa only [d318086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37513 p hg
    simpa only [d318086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37515 (p : Pattern) (guard : d318087 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318086 p = 1 := by simpa only [d318087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37514 p hg
    simpa only [d318087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37516 (p : Pattern) (guard : d318088 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318087 p = 1 := by simpa only [d318088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37515 p hg
    simpa only [d318088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37517 (p : Pattern) (guard : d318089 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318088 p = 1 := by simpa only [d318089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37516 p hg
    simpa only [d318089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37518 (p : Pattern) (guard : d318090 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d318011 p = 1 := by simpa only [d318090, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37396 p hg
    simpa only [d318090, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318089 p = 1 := by simpa only [d318090, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37517 p hg
    simpa only [d318090, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37519 (p : Pattern) (guard : d318085 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318006 p = 1 := by simpa only [d318085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37391 p hg
    simpa only [d318085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37520 (p : Pattern) (guard : d318086 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318085 p = 1 := by simpa only [d318086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37519 p hg
    simpa only [d318086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37521 (p : Pattern) (guard : d318087 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318086 p = 1 := by simpa only [d318087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37520 p hg
    simpa only [d318087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37522 (p : Pattern) (guard : d318088 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318087 p = 1 := by simpa only [d318088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37521 p hg
    simpa only [d318088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37523 (p : Pattern) (guard : d318089 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318088 p = 1 := by simpa only [d318089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37522 p hg
    simpa only [d318089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37524 (p : Pattern) (guard : d318091 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318016 p = 1 := by simpa only [d318091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37398 p hg
    simpa only [d318091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37525 (p : Pattern) (guard : d318092 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318091 p = 1 := by simpa only [d318092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37524 p hg
    simpa only [d318092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37526 (p : Pattern) (guard : d318093 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318092 p = 1 := by simpa only [d318093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37525 p hg
    simpa only [d318093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37527 (p : Pattern) (guard : d318094 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318093 p = 1 := by simpa only [d318094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37526 p hg
    simpa only [d318094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37528 (p : Pattern) (guard : d318095 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318094 p = 1 := by simpa only [d318095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37527 p hg
    simpa only [d318095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37529 (p : Pattern) (guard : d318096 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d318089 p = 1 := by simpa only [d318096, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37523 p hg
    simpa only [d318096, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318095 p = 1 := by simpa only [d318096, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37528 p hg
    simpa only [d318096, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37530 (p : Pattern) (guard : d318097 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d318090 p = 1 := by simpa only [d318097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37518 p hg
    simpa only [d318097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318096 p = 1 := by simpa only [d318097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37529 p hg
    simpa only [d318097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37531 (p : Pattern) (guard : d318098 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318084 p = 1 := by simpa only [d318098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37512 p hg
    simpa only [d318098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318097 p = 1 := by simpa only [d318098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37530 p hg
    simpa only [d318098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37532 (p : Pattern) (guard : d318099 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318098 p = 1 := by simpa only [d318099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37531 p hg
    simpa only [d318099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d318099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37533 (p : Pattern) (guard : d318100 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318025 p = 1 := by simpa only [d318100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37407 p hg
    simpa only [d318100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318099 p = 1 := by simpa only [d318100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37532 p hg
    simpa only [d318100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37534 (p : Pattern) (guard : d2013 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare37535 (p : Pattern) (guard : d2027 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37534 p hg
    simpa only [d2027, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d2027, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37536 (p : Pattern) (guard : d2028 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37535 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37537 (p : Pattern) (guard : d2029 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37536 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37538 (p : Pattern) (guard : d2030 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37537 p hg
    simpa only [d2030, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d2030, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37539 (p : Pattern) (guard : d2031 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37538 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37540 (p : Pattern) (guard : d317063 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37539 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37541 (p : Pattern) (guard : d317064 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317063 p = 1 := by simpa only [d317064, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37540 p hg
    simpa only [d317064, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317064, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d317064, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37542 (p : Pattern) (guard : d317065 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317064 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37541 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37543 (p : Pattern) (guard : d317066 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317065 p = 1 := by simpa only [d317066, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37542 p hg
    simpa only [d317066, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317066, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317066, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37544 (p : Pattern) (guard : d317067 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317066 p = 1 := by simpa only [d317067, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37543 p hg
    simpa only [d317067, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317067, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317067, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37545 (p : Pattern) (guard : d317068 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317068, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317068, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317067 p = 1 := by simpa only [d317068, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37544 p hg
    simpa only [d317068, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37546 (p : Pattern) (guard : d317069 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317068 p = 1 := by simpa only [d317069, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37545 p hg
    simpa only [d317069, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317069, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317069, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37547 (p : Pattern) (guard : d317070 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37541 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37548 (p : Pattern) (guard : d317071 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317070 p = 1 := by simpa only [d317071, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37547 p hg
    simpa only [d317071, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317071, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317071, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37549 (p : Pattern) (guard : d317072 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317071 p = 1 := by simpa only [d317072, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37548 p hg
    simpa only [d317072, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317072, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317072, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37550 (p : Pattern) (guard : d317073 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317073, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317073, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317072 p = 1 := by simpa only [d317073, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37549 p hg
    simpa only [d317073, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37551 (p : Pattern) (guard : d317074 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317073 p = 1 := by simpa only [d317074, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37550 p hg
    simpa only [d317074, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317074, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317074, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37552 (p : Pattern) (guard : d317075 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317069 p = 1 := by simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37546 p hg
    simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317074 p = 1 := by simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37551 p hg
    simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37553 (p : Pattern) (guard : d317076 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317075 p = 1 := by simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37552 p hg
    simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37554 (p : Pattern) (guard : d317163 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317076 p = 1 := by simpa only [d317163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37553 p hg
    simpa only [d317163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37555 (p : Pattern) (guard : d317164 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317164, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317164, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317163 p = 1 := by simpa only [d317164, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37554 p hg
    simpa only [d317164, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37556 (p : Pattern) (guard : d317165 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317165, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317165, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317164 p = 1 := by simpa only [d317165, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37555 p hg
    simpa only [d317165, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37557 (p : Pattern) (guard : d317166 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317076 p = 1 := by simpa only [d317166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37553 p hg
    simpa only [d317166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37558 (p : Pattern) (guard : d317167 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317167, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317167, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317166 p = 1 := by simpa only [d317167, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37557 p hg
    simpa only [d317167, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37559 (p : Pattern) (guard : d317168 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317168, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317168, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317167 p = 1 := by simpa only [d317168, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37558 p hg
    simpa only [d317168, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37560 (p : Pattern) (guard : d317169 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317165 p = 1 := by simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37556 p hg
    simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317168 p = 1 := by simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37559 p hg
    simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37561 (p : Pattern) (guard : d27032 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37538 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37562 (p : Pattern) (guard : d235783 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37561 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37563 (p : Pattern) (guard : d235784 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d235783 p = 1 := by simpa only [d235784, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37562 p hg
    simpa only [d235784, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d235784, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d235784, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37564 (p : Pattern) (guard : d317976 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37541 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235784 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37563 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37565 (p : Pattern) (guard : d317977 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317976 p = 1 := by simpa only [d317977, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37564 p hg
    simpa only [d317977, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317977, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317977, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37566 (p : Pattern) (guard : d317978 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317977 p = 1 := by simpa only [d317978, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37565 p hg
    simpa only [d317978, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317978, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317978, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37567 (p : Pattern) (guard : d317979 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317979, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317979, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317978 p = 1 := by simpa only [d317979, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37566 p hg
    simpa only [d317979, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37568 (p : Pattern) (guard : d317980 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317979 p = 1 := by simpa only [d317980, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37567 p hg
    simpa only [d317980, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317980, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317980, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37569 (p : Pattern) (guard : d317094 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d235784 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37563 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37570 (p : Pattern) (guard : d317095 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317094 p = 1 := by simpa only [d317095, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37569 p hg
    simpa only [d317095, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317095, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317095, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37571 (p : Pattern) (guard : d317096 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317095 p = 1 := by simpa only [d317096, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37570 p hg
    simpa only [d317096, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317096, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317096, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37572 (p : Pattern) (guard : d317097 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317097, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317097, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317096 p = 1 := by simpa only [d317097, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37571 p hg
    simpa only [d317097, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37573 (p : Pattern) (guard : d317098 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317097 p = 1 := by simpa only [d317098, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37572 p hg
    simpa only [d317098, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317098, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317098, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37574 (p : Pattern) (guard : d317981 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317980 p = 1 := by simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37568 p hg
    simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317098 p = 1 := by simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37573 p hg
    simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37575 (p : Pattern) (guard : d317982 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317981 p = 1 := by simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37574 p hg
    simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37576 (p : Pattern) (guard : d317983 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317076 p = 1 := by simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37553 p hg
    simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317982 p = 1 := by simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37575 p hg
    simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37577 (p : Pattern) (guard : d317984 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317984, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317984, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317983 p = 1 := by simpa only [d317984, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37576 p hg
    simpa only [d317984, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37578 (p : Pattern) (guard : d317985 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317985, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317985, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317984 p = 1 := by simpa only [d317985, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37577 p hg
    simpa only [d317985, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37579 (p : Pattern) (guard : d317099 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317098 p = 1 := by simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37573 p hg
    simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37580 (p : Pattern) (guard : d317100 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317099 p = 1 := by simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37579 p hg
    simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37581 (p : Pattern) (guard : d317986 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317982 p = 1 := by simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37575 p hg
    simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317100 p = 1 := by simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37580 p hg
    simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37582 (p : Pattern) (guard : d317987 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317987, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317987, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317986 p = 1 := by simpa only [d317987, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37581 p hg
    simpa only [d317987, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37583 (p : Pattern) (guard : d317988 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317988, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317988, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317987 p = 1 := by simpa only [d317988, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37582 p hg
    simpa only [d317988, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37584 (p : Pattern) (guard : d317989 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317985 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37578 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317988 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37583 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37585 (p : Pattern) (guard : d318043 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317169 p = 1 := by simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37560 p hg
    simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317989 p = 1 := by simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37584 p hg
    simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37586 (p : Pattern) (guard : d318044 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d318043 p = 1 := by simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37585 p hg
    simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37587 (p : Pattern) (guard : d318045 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d318044 p = 1 := by simpa only [d318045, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37586 p hg
    simpa only [d318045, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318045, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d318045, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37588 (p : Pattern) (guard : d318046 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318046, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d318046, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318045 p = 1 := by simpa only [d318046, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37587 p hg
    simpa only [d318046, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37589 (p : Pattern) (guard : d317990 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317988 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37583 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37590 (p : Pattern) (guard : d317991 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317989 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37584 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317990 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37589 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37591 (p : Pattern) (guard : d317992 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317991 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37590 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37592 (p : Pattern) (guard : d317993 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317992 p = 1 := by simpa only [d317993, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37591 p hg
    simpa only [d317993, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317993, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d317993, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37593 (p : Pattern) (guard : d317994 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317994, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d317994, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317993 p = 1 := by simpa only [d317994, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37592 p hg
    simpa only [d317994, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37594 (p : Pattern) (guard : d318047 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d318046 p = 1 := by simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37588 p hg
    simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317994 p = 1 := by simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37593 p hg
    simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37595 (p : Pattern) (guard : d318048 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318047 p = 1 := by simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37594 p hg
    simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37596 (p : Pattern) (guard : d318049 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318048 p = 1 := by simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37595 p hg
    simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37597 (p : Pattern) (guard : d318074 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318049 p = 1 := by simpa only [d318074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37596 p hg
    simpa only [d318074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37598 (p : Pattern) (guard : d317995 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317990 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37589 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37599 (p : Pattern) (guard : d317996 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317995 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37598 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37600 (p : Pattern) (guard : d317997 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317996 p = 1 := by simpa only [d317997, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37599 p hg
    simpa only [d317997, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317997, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d317997, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37601 (p : Pattern) (guard : d317998 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317998, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d317998, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317997 p = 1 := by simpa only [d317998, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37600 p hg
    simpa only [d317998, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37602 (p : Pattern) (guard : d317999 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317994 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37593 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317998 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37601 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37603 (p : Pattern) (guard : d318000 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317999 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37602 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37604 (p : Pattern) (guard : d318001 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318000 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37603 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37605 (p : Pattern) (guard : d318015 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318001 p = 1 := by simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37604 p hg
    simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37606 (p : Pattern) (guard : d318075 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318074 p = 1 := by simpa only [d318075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37597 p hg
    simpa only [d318075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318015 p = 1 := by simpa only [d318075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37605 p hg
    simpa only [d318075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37607 (p : Pattern) (guard : d318076 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318075 p = 1 := by simpa only [d318076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37606 p hg
    simpa only [d318076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37608 (p : Pattern) (guard : d318053 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317994 p = 1 := by simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37593 p hg
    simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37609 (p : Pattern) (guard : d318054 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318053 p = 1 := by simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37608 p hg
    simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37610 (p : Pattern) (guard : d318055 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318054 p = 1 := by simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37609 p hg
    simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37611 (p : Pattern) (guard : d318077 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318055 p = 1 := by simpa only [d318077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37610 p hg
    simpa only [d318077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37612 (p : Pattern) (guard : d318078 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318077 p = 1 := by simpa only [d318078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37611 p hg
    simpa only [d318078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37613 (p : Pattern) (guard : d318079 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318078 p = 1 := by simpa only [d318079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37612 p hg
    simpa only [d318079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37614 (p : Pattern) (guard : d318080 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318076 p = 1 := by simpa only [d318080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37607 p hg
    simpa only [d318080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318079 p = 1 := by simpa only [d318080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37613 p hg
    simpa only [d318080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37615 (p : Pattern) (guard : d318101 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318080 p = 1 := by simpa only [d318101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37614 p hg
    simpa only [d318101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37616 (p : Pattern) (guard : d318102 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318101 p = 1 := by simpa only [d318102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37615 p hg
    simpa only [d318102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37617 (p : Pattern) (guard : d318103 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318103, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318103, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318102 p = 1 := by simpa only [d318103, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37616 p hg
    simpa only [d318103, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37618 (p : Pattern) (guard : d318104 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d318104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318103 p = 1 := by simpa only [d318104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37617 p hg
    simpa only [d318104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37619 (p : Pattern) (guard : d318003 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317998 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37601 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37620 (p : Pattern) (guard : d318004 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318003 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37619 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37621 (p : Pattern) (guard : d318005 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318004 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37620 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37622 (p : Pattern) (guard : d318016 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318005 p = 1 := by simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37621 p hg
    simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37623 (p : Pattern) (guard : d318091 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318016 p = 1 := by simpa only [d318091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37622 p hg
    simpa only [d318091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37624 (p : Pattern) (guard : d318092 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318091 p = 1 := by simpa only [d318092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37623 p hg
    simpa only [d318092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37625 (p : Pattern) (guard : d318093 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318092 p = 1 := by simpa only [d318093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37624 p hg
    simpa only [d318093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37626 (p : Pattern) (guard : d318094 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318093 p = 1 := by simpa only [d318094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37625 p hg
    simpa only [d318094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37627 (p : Pattern) (guard : d318095 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d318095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318094 p = 1 := by simpa only [d318095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37626 p hg
    simpa only [d318095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37628 (p : Pattern) (guard : d318105 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318105, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318105, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318095 p = 1 := by simpa only [d318105, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37627 p hg
    simpa only [d318105, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37629 (p : Pattern) (guard : d318106 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d318106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318105 p = 1 := by simpa only [d318106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37628 p hg
    simpa only [d318106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37630 (p : Pattern) (guard : d318107 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318104 p = 1 := by simpa only [d318107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37618 p hg
    simpa only [d318107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318106 p = 1 := by simpa only [d318107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37629 p hg
    simpa only [d318107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37631 (p : Pattern) (guard : d318108 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318107 p = 1 := by simpa only [d318108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37630 p hg
    simpa only [d318108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d318108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37632 (p : Pattern) (guard : d318109 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318108 p = 1 := by simpa only [d318109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37631 p hg
    simpa only [d318109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d318109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37633 (p : Pattern) (guard : d318110 p = 1) : d50390 p ≤ (3 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318100 p = 1 := by simpa only [d318110, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37533 p hg
    simpa only [d318110, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318109 p = 1 := by simpa only [d318110, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37632 p hg
    simpa only [d318110, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37634 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare37635 (p : Pattern) (guard : d2027 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37634 p hg
    simpa only [d2027, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d2027, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37636 (p : Pattern) (guard : d2028 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37635 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37637 (p : Pattern) (guard : d2029 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37636 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37638 (p : Pattern) (guard : d2030 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37637 p hg
    simpa only [d2030, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d2030, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37639 (p : Pattern) (guard : d2031 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37638 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37640 (p : Pattern) (guard : d317063 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37639 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37641 (p : Pattern) (guard : d317064 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317063 p = 1 := by simpa only [d317064, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37640 p hg
    simpa only [d317064, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317064, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d317064, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37642 (p : Pattern) (guard : d317065 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317064 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37641 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37643 (p : Pattern) (guard : d317253 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317065 p = 1 := by simpa only [d317253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37642 p hg
    simpa only [d317253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37644 (p : Pattern) (guard : d317066 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317065 p = 1 := by simpa only [d317066, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37311 p hg
    simpa only [d317066, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317066, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317066, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37645 (p : Pattern) (guard : d317254 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317253 p = 1 := by simpa only [d317254, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37643 p hg
    simpa only [d317254, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317066 p = 1 := by simpa only [d317254, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37644 p hg
    simpa only [d317254, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37646 (p : Pattern) (guard : d2013 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare37647 (p : Pattern) (guard : d2027 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37646 p hg
    simpa only [d2027, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d2027, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37648 (p : Pattern) (guard : d2028 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37647 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37649 (p : Pattern) (guard : d2029 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37648 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37650 (p : Pattern) (guard : d2030 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37649 p hg
    simpa only [d2030, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d2030, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37651 (p : Pattern) (guard : d2031 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37650 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37652 (p : Pattern) (guard : d317063 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37651 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37653 (p : Pattern) (guard : d317064 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317063 p = 1 := by simpa only [d317064, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37652 p hg
    simpa only [d317064, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317064, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d317064, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37654 (p : Pattern) (guard : d317065 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317064 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37653 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37655 (p : Pattern) (guard : d317066 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317065 p = 1 := by simpa only [d317066, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37654 p hg
    simpa only [d317066, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317066, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317066, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37656 (p : Pattern) (guard : d317067 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317066 p = 1 := by simpa only [d317067, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37655 p hg
    simpa only [d317067, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317067, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317067, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37657 (p : Pattern) (guard : d317255 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317254 p = 1 := by simpa only [d317255, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37645 p hg
    simpa only [d317255, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317067 p = 1 := by simpa only [d317255, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37656 p hg
    simpa only [d317255, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37658 (p : Pattern) (guard : d317256 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317255 p = 1 := by simpa only [d317256, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37657 p hg
    simpa only [d317256, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317256, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317256, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37659 (p : Pattern) (guard : d317070 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37641 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37660 (p : Pattern) (guard : d317257 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317070 p = 1 := by simpa only [d317257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37659 p hg
    simpa only [d317257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37661 (p : Pattern) (guard : d317071 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317070 p = 1 := by simpa only [d317071, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37316 p hg
    simpa only [d317071, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317071, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317071, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37662 (p : Pattern) (guard : d317258 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317257 p = 1 := by simpa only [d317258, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37660 p hg
    simpa only [d317258, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317071 p = 1 := by simpa only [d317258, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37661 p hg
    simpa only [d317258, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37663 (p : Pattern) (guard : d317070 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37653 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37664 (p : Pattern) (guard : d317071 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317070 p = 1 := by simpa only [d317071, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37663 p hg
    simpa only [d317071, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317071, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317071, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37665 (p : Pattern) (guard : d317072 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317071 p = 1 := by simpa only [d317072, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37664 p hg
    simpa only [d317072, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317072, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317072, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37666 (p : Pattern) (guard : d317259 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317258 p = 1 := by simpa only [d317259, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37662 p hg
    simpa only [d317259, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317072 p = 1 := by simpa only [d317259, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37665 p hg
    simpa only [d317259, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37667 (p : Pattern) (guard : d317260 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317259 p = 1 := by simpa only [d317260, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37666 p hg
    simpa only [d317260, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317260, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317260, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37668 (p : Pattern) (guard : d317261 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317256 p = 1 := by simpa only [d317261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37658 p hg
    simpa only [d317261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317260 p = 1 := by simpa only [d317261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37667 p hg
    simpa only [d317261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37669 (p : Pattern) (guard : d317262 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317261 p = 1 := by simpa only [d317262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37668 p hg
    simpa only [d317262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37670 (p : Pattern) (guard : d317263 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317262 p = 1 := by simpa only [d317263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37669 p hg
    simpa only [d317263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37671 (p : Pattern) (guard : d317264 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317264, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317264, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317263 p = 1 := by simpa only [d317264, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37670 p hg
    simpa only [d317264, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37672 (p : Pattern) (guard : d317265 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317265, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317265, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317264 p = 1 := by simpa only [d317265, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37671 p hg
    simpa only [d317265, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37673 (p : Pattern) (guard : d317266 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317262 p = 1 := by simpa only [d317266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37669 p hg
    simpa only [d317266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37674 (p : Pattern) (guard : d317267 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317267, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317267, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317266 p = 1 := by simpa only [d317267, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37673 p hg
    simpa only [d317267, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37675 (p : Pattern) (guard : d317268 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317268, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317268, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317267 p = 1 := by simpa only [d317268, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37674 p hg
    simpa only [d317268, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37676 (p : Pattern) (guard : d317269 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317265 p = 1 := by simpa only [d317269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37672 p hg
    simpa only [d317269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317268 p = 1 := by simpa only [d317269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37675 p hg
    simpa only [d317269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37677 (p : Pattern) (guard : d27032 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37638 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37678 (p : Pattern) (guard : d235783 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37677 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37679 (p : Pattern) (guard : d235784 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d235783 p = 1 := by simpa only [d235784, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37678 p hg
    simpa only [d235784, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d235784, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d235784, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37680 (p : Pattern) (guard : d317976 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37641 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235784 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37679 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37681 (p : Pattern) (guard : d318111 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d318111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317976 p = 1 := by simpa only [d318111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37680 p hg
    simpa only [d318111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37682 (p : Pattern) (guard : d317977 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317976 p = 1 := by simpa only [d317977, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37326 p hg
    simpa only [d317977, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317977, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317977, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37683 (p : Pattern) (guard : d318112 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d318111 p = 1 := by simpa only [d318112, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37681 p hg
    simpa only [d318112, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317977 p = 1 := by simpa only [d318112, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37682 p hg
    simpa only [d318112, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37684 (p : Pattern) (guard : d27032 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37650 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37685 (p : Pattern) (guard : d235783 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37684 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37686 (p : Pattern) (guard : d235784 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d235783 p = 1 := by simpa only [d235784, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37685 p hg
    simpa only [d235784, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d235784, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d235784, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37687 (p : Pattern) (guard : d317976 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37653 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235784 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37686 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37688 (p : Pattern) (guard : d317977 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317976 p = 1 := by simpa only [d317977, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37687 p hg
    simpa only [d317977, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317977, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317977, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37689 (p : Pattern) (guard : d317978 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317977 p = 1 := by simpa only [d317978, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37688 p hg
    simpa only [d317978, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317978, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317978, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37690 (p : Pattern) (guard : d318113 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d318112 p = 1 := by simpa only [d318113, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37683 p hg
    simpa only [d318113, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317978 p = 1 := by simpa only [d318113, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37689 p hg
    simpa only [d318113, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37691 (p : Pattern) (guard : d318114 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d318113 p = 1 := by simpa only [d318114, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37690 p hg
    simpa only [d318114, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318114, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d318114, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37692 (p : Pattern) (guard : d317094 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d235784 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37679 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37693 (p : Pattern) (guard : d317283 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317094 p = 1 := by simpa only [d317283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37692 p hg
    simpa only [d317283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37694 (p : Pattern) (guard : d317095 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317094 p = 1 := by simpa only [d317095, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37331 p hg
    simpa only [d317095, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317095, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317095, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37695 (p : Pattern) (guard : d317284 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317283 p = 1 := by simpa only [d317284, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37693 p hg
    simpa only [d317284, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317095 p = 1 := by simpa only [d317284, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37694 p hg
    simpa only [d317284, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37696 (p : Pattern) (guard : d317094 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d235784 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37686 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37697 (p : Pattern) (guard : d317095 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317094 p = 1 := by simpa only [d317095, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37696 p hg
    simpa only [d317095, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317095, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317095, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37698 (p : Pattern) (guard : d317096 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317095 p = 1 := by simpa only [d317096, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37697 p hg
    simpa only [d317096, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317096, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317096, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37699 (p : Pattern) (guard : d317285 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317284 p = 1 := by simpa only [d317285, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37695 p hg
    simpa only [d317285, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317096 p = 1 := by simpa only [d317285, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37698 p hg
    simpa only [d317285, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37700 (p : Pattern) (guard : d317286 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317285 p = 1 := by simpa only [d317286, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37699 p hg
    simpa only [d317286, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317286, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317286, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37701 (p : Pattern) (guard : d318115 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d318114 p = 1 := by simpa only [d318115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37691 p hg
    simpa only [d318115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317286 p = 1 := by simpa only [d318115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37700 p hg
    simpa only [d318115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37702 (p : Pattern) (guard : d318116 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d318115 p = 1 := by simpa only [d318116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37701 p hg
    simpa only [d318116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d318116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37703 (p : Pattern) (guard : d318117 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317262 p = 1 := by simpa only [d318117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37669 p hg
    simpa only [d318117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318116 p = 1 := by simpa only [d318117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37702 p hg
    simpa only [d318117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37704 (p : Pattern) (guard : d318118 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318118, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d318118, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318117 p = 1 := by simpa only [d318118, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37703 p hg
    simpa only [d318118, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37705 (p : Pattern) (guard : d318119 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318119, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d318119, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318118 p = 1 := by simpa only [d318119, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37704 p hg
    simpa only [d318119, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37706 (p : Pattern) (guard : d317287 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317286 p = 1 := by simpa only [d317287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37700 p hg
    simpa only [d317287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37707 (p : Pattern) (guard : d317288 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317287 p = 1 := by simpa only [d317288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37706 p hg
    simpa only [d317288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37708 (p : Pattern) (guard : d318120 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d318116 p = 1 := by simpa only [d318120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37702 p hg
    simpa only [d318120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317288 p = 1 := by simpa only [d318120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37707 p hg
    simpa only [d318120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37709 (p : Pattern) (guard : d318121 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318121, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d318121, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318120 p = 1 := by simpa only [d318121, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37708 p hg
    simpa only [d318121, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37710 (p : Pattern) (guard : d318122 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318122, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d318122, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318121 p = 1 := by simpa only [d318122, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37709 p hg
    simpa only [d318122, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37711 (p : Pattern) (guard : d318123 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d318119 p = 1 := by simpa only [d318123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37705 p hg
    simpa only [d318123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318122 p = 1 := by simpa only [d318123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37710 p hg
    simpa only [d318123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37712 (p : Pattern) (guard : d318124 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317269 p = 1 := by simpa only [d318124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37676 p hg
    simpa only [d318124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318123 p = 1 := by simpa only [d318124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37711 p hg
    simpa only [d318124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37713 (p : Pattern) (guard : d318125 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d318124 p = 1 := by simpa only [d318125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37712 p hg
    simpa only [d318125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d318125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37714 (p : Pattern) (guard : d318126 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d318125 p = 1 := by simpa only [d318126, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37713 p hg
    simpa only [d318126, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318126, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d318126, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37715 (p : Pattern) (guard : d318127 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318127, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d318127, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318126 p = 1 := by simpa only [d318127, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37714 p hg
    simpa only [d318127, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37716 (p : Pattern) (guard : d318128 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d318122 p = 1 := by simpa only [d318128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37710 p hg
    simpa only [d318128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d318128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37717 (p : Pattern) (guard : d318129 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d318123 p = 1 := by simpa only [d318129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37711 p hg
    simpa only [d318129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318128 p = 1 := by simpa only [d318129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37716 p hg
    simpa only [d318129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37718 (p : Pattern) (guard : d318130 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d318129 p = 1 := by simpa only [d318130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37717 p hg
    simpa only [d318130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d318130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37719 (p : Pattern) (guard : d318131 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d318130 p = 1 := by simpa only [d318131, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37718 p hg
    simpa only [d318131, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318131, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d318131, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37720 (p : Pattern) (guard : d318132 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318132, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d318132, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318131 p = 1 := by simpa only [d318132, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37719 p hg
    simpa only [d318132, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37721 (p : Pattern) (guard : d318133 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d318127 p = 1 := by simpa only [d318133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37715 p hg
    simpa only [d318133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318132 p = 1 := by simpa only [d318133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37720 p hg
    simpa only [d318133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37722 (p : Pattern) (guard : d318134 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318133 p = 1 := by simpa only [d318134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37721 p hg
    simpa only [d318134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37723 (p : Pattern) (guard : d318135 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318134 p = 1 := by simpa only [d318135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37722 p hg
    simpa only [d318135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37724 (p : Pattern) (guard : d318136 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318135 p = 1 := by simpa only [d318136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37723 p hg
    simpa only [d318136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37725 (p : Pattern) (guard : d318137 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d318128 p = 1 := by simpa only [d318137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37716 p hg
    simpa only [d318137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d318137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37726 (p : Pattern) (guard : d318138 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d318137 p = 1 := by simpa only [d318138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37725 p hg
    simpa only [d318138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d318138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37727 (p : Pattern) (guard : d318139 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d318138 p = 1 := by simpa only [d318139, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37726 p hg
    simpa only [d318139, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318139, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d318139, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37728 (p : Pattern) (guard : d318140 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318140, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d318140, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318139 p = 1 := by simpa only [d318140, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37727 p hg
    simpa only [d318140, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37729 (p : Pattern) (guard : d318141 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d318132 p = 1 := by simpa only [d318141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37720 p hg
    simpa only [d318141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318140 p = 1 := by simpa only [d318141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37728 p hg
    simpa only [d318141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37730 (p : Pattern) (guard : d318142 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318141 p = 1 := by simpa only [d318142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37729 p hg
    simpa only [d318142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37731 (p : Pattern) (guard : d318143 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318142 p = 1 := by simpa only [d318143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37730 p hg
    simpa only [d318143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37732 (p : Pattern) (guard : d318144 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318143 p = 1 := by simpa only [d318144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37731 p hg
    simpa only [d318144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37733 (p : Pattern) (guard : d318145 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318136 p = 1 := by simpa only [d318145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37724 p hg
    simpa only [d318145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318144 p = 1 := by simpa only [d318145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37732 p hg
    simpa only [d318145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37734 (p : Pattern) (guard : d318146 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318145 p = 1 := by simpa only [d318146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37733 p hg
    simpa only [d318146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37735 (p : Pattern) (guard : d318147 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d318132 p = 1 := by simpa only [d318147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37720 p hg
    simpa only [d318147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37736 (p : Pattern) (guard : d318148 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318147 p = 1 := by simpa only [d318148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37735 p hg
    simpa only [d318148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37737 (p : Pattern) (guard : d318149 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318148 p = 1 := by simpa only [d318149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37736 p hg
    simpa only [d318149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37738 (p : Pattern) (guard : d318150 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318149 p = 1 := by simpa only [d318150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37737 p hg
    simpa only [d318150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37739 (p : Pattern) (guard : d318151 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318150 p = 1 := by simpa only [d318151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37738 p hg
    simpa only [d318151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37740 (p : Pattern) (guard : d318152 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318151 p = 1 := by simpa only [d318152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37739 p hg
    simpa only [d318152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37741 (p : Pattern) (guard : d318153 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318146 p = 1 := by simpa only [d318153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37734 p hg
    simpa only [d318153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318152 p = 1 := by simpa only [d318153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37740 p hg
    simpa only [d318153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37742 (p : Pattern) (guard : d318154 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318153 p = 1 := by simpa only [d318154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37741 p hg
    simpa only [d318154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37743 (p : Pattern) (guard : d318155 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318154 p = 1 := by simpa only [d318155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37742 p hg
    simpa only [d318155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37744 (p : Pattern) (guard : d318156 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318156, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318156, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318155 p = 1 := by simpa only [d318156, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37743 p hg
    simpa only [d318156, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37745 (p : Pattern) (guard : d318157 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d318157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318156 p = 1 := by simpa only [d318157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37744 p hg
    simpa only [d318157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37746 (p : Pattern) (guard : d318158 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d318140 p = 1 := by simpa only [d318158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37728 p hg
    simpa only [d318158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37747 (p : Pattern) (guard : d318159 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318158 p = 1 := by simpa only [d318159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37746 p hg
    simpa only [d318159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37748 (p : Pattern) (guard : d318160 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318159 p = 1 := by simpa only [d318160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37747 p hg
    simpa only [d318160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37749 (p : Pattern) (guard : d318161 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318160 p = 1 := by simpa only [d318161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37748 p hg
    simpa only [d318161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318161, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
