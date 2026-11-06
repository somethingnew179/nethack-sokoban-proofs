import NetHack.Soko22Hazard87.Compare045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11500 (p : Pattern) (guard : d160187 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160186 p = 1 := by simpa only [d160187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11499 p hg
    simpa only [d160187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11501 (p : Pattern) (guard : d160188 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160187 p = 1 := by simpa only [d160188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11500 p hg
    simpa only [d160188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11502 (p : Pattern) (guard : d160189 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160188 p = 1 := by simpa only [d160189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11501 p hg
    simpa only [d160189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11503 (p : Pattern) (guard : d160190 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160183 p = 1 := by simpa only [d160190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d160190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160189 p = 1 := by simpa only [d160190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d160190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11504 (p : Pattern) (guard : d160191 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d160167 p = 1 := by simpa only [d160191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11478 p hg
    simpa only [d160191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160190 p = 1 := by simpa only [d160191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11503 p hg
    simpa only [d160191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11505 (p : Pattern) (guard : d160192 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d160158 p = 1 := by simpa only [d160192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11469 p hg
    simpa only [d160192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160191 p = 1 := by simpa only [d160192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11504 p hg
    simpa only [d160192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11506 (p : Pattern) (guard : d160193 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160192 p = 1 := by simpa only [d160193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11505 p hg
    simpa only [d160193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11507 (p : Pattern) (guard : d160194 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160151 p = 1 := by simpa only [d160194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d160194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11508 (p : Pattern) (guard : d160195 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160153 p = 1 := by simpa only [d160195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11464 p hg
    simpa only [d160195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11509 (p : Pattern) (guard : d160196 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160194 p = 1 := by simpa only [d160196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d160196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160195 p = 1 := by simpa only [d160196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11508 p hg
    simpa only [d160196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11510 (p : Pattern) (guard : d160197 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160196 p = 1 := by simpa only [d160197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11509 p hg
    simpa only [d160197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11511 (p : Pattern) (guard : d160198 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160197 p = 1 := by simpa only [d160198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11510 p hg
    simpa only [d160198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11512 (p : Pattern) (guard : d160199 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160198 p = 1 := by simpa only [d160199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11511 p hg
    simpa only [d160199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11513 (p : Pattern) (guard : d160200 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160160 p = 1 := by simpa only [d160200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d160200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11514 (p : Pattern) (guard : d160201 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160163 p = 1 := by simpa only [d160201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11474 p hg
    simpa only [d160201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11515 (p : Pattern) (guard : d160202 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160200 p = 1 := by simpa only [d160202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11513 p hg
    simpa only [d160202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160201 p = 1 := by simpa only [d160202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11514 p hg
    simpa only [d160202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11516 (p : Pattern) (guard : d160203 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160202 p = 1 := by simpa only [d160203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11515 p hg
    simpa only [d160203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11517 (p : Pattern) (guard : d160204 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160203 p = 1 := by simpa only [d160204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11516 p hg
    simpa only [d160204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11518 (p : Pattern) (guard : d160205 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160180 p = 1 := by simpa only [d160205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11493 p hg
    simpa only [d160205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11519 (p : Pattern) (guard : d160206 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160205 p = 1 := by simpa only [d160206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11518 p hg
    simpa only [d160206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160140 p = 1 := by simpa only [d160206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11451 p hg
    simpa only [d160206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11520 (p : Pattern) (guard : d160207 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160206 p = 1 := by simpa only [d160207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d160207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11521 (p : Pattern) (guard : d160208 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160186 p = 1 := by simpa only [d160208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11499 p hg
    simpa only [d160208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11522 (p : Pattern) (guard : d160209 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160208 p = 1 := by simpa only [d160209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11521 p hg
    simpa only [d160209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11523 (p : Pattern) (guard : d160210 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160209 p = 1 := by simpa only [d160210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11522 p hg
    simpa only [d160210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11524 (p : Pattern) (guard : d160211 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160207 p = 1 := by simpa only [d160211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11520 p hg
    simpa only [d160211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160210 p = 1 := by simpa only [d160211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11523 p hg
    simpa only [d160211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11525 (p : Pattern) (guard : d160212 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d160204 p = 1 := by simpa only [d160212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11517 p hg
    simpa only [d160212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160211 p = 1 := by simpa only [d160212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11524 p hg
    simpa only [d160212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11526 (p : Pattern) (guard : d160213 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d160199 p = 1 := by simpa only [d160213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11512 p hg
    simpa only [d160213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160212 p = 1 := by simpa only [d160213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11525 p hg
    simpa only [d160213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11527 (p : Pattern) (guard : d160214 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160192 p = 1 := by simpa only [d160214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11505 p hg
    simpa only [d160214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160213 p = 1 := by simpa only [d160214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11526 p hg
    simpa only [d160214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11528 (p : Pattern) (guard : d160215 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160193 p = 1 := by simpa only [d160215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11506 p hg
    simpa only [d160215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160214 p = 1 := by simpa only [d160215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11527 p hg
    simpa only [d160215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11529 (p : Pattern) (guard : d160216 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160131 p = 1 := by simpa only [d160216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11442 p hg
    simpa only [d160216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11530 (p : Pattern) (guard : d160217 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160216 p = 1 := by simpa only [d160217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11529 p hg
    simpa only [d160217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11531 (p : Pattern) (guard : d160218 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160217 p = 1 := by simpa only [d160218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11530 p hg
    simpa only [d160218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11532 (p : Pattern) (guard : d160219 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160218 p = 1 := by simpa only [d160219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11531 p hg
    simpa only [d160219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11533 (p : Pattern) (guard : d160220 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160219 p = 1 := by simpa only [d160220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11532 p hg
    simpa only [d160220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11534 (p : Pattern) (guard : d160221 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160136 p = 1 := by simpa only [d160221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11447 p hg
    simpa only [d160221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160220 p = 1 := by simpa only [d160221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11533 p hg
    simpa only [d160221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11535 (p : Pattern) (guard : d160222 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160141 p = 1 := by simpa only [d160222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11452 p hg
    simpa only [d160222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11536 (p : Pattern) (guard : d160223 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160222 p = 1 := by simpa only [d160223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11535 p hg
    simpa only [d160223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11537 (p : Pattern) (guard : d160224 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160223 p = 1 := by simpa only [d160224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11536 p hg
    simpa only [d160224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11538 (p : Pattern) (guard : d160225 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160224 p = 1 := by simpa only [d160225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11537 p hg
    simpa only [d160225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11539 (p : Pattern) (guard : d160226 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160225 p = 1 := by simpa only [d160226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11538 p hg
    simpa only [d160226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11540 (p : Pattern) (guard : d160227 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160220 p = 1 := by simpa only [d160227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11533 p hg
    simpa only [d160227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160226 p = 1 := by simpa only [d160227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11539 p hg
    simpa only [d160227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11541 (p : Pattern) (guard : d160228 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160221 p = 1 := by simpa only [d160228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11534 p hg
    simpa only [d160228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160227 p = 1 := by simpa only [d160228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11540 p hg
    simpa only [d160228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11542 (p : Pattern) (guard : d160229 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160215 p = 1 := by simpa only [d160229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11528 p hg
    simpa only [d160229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160228 p = 1 := by simpa only [d160229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11541 p hg
    simpa only [d160229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11543 (p : Pattern) (guard : d160230 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160229 p = 1 := by simpa only [d160230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11542 p hg
    simpa only [d160230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11544 (p : Pattern) (guard : d160231 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160150 p = 1 := by simpa only [d160231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d160231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160230 p = 1 := by simpa only [d160231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11543 p hg
    simpa only [d160231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11545 (p : Pattern) (guard : d545 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d545, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5200 p hg
    simpa only [d545, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11546 (p : Pattern) (guard : d546 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11545 p hg
    simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11547 (p : Pattern) (guard : d160168 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d546 p = 1 := by simpa only [d160168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11546 p hg
    simpa only [d160168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11548 (p : Pattern) (guard : d160169 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160168 p = 1 := by simpa only [d160169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11547 p hg
    simpa only [d160169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11549 (p : Pattern) (guard : d160170 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160169 p = 1 := by simpa only [d160170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11548 p hg
    simpa only [d160170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160001 p = 1 := by simpa only [d160170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11330 p hg
    simpa only [d160170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11550 (p : Pattern) (guard : d160171 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160171, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160171, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160170 p = 1 := by simpa only [d160171, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11549 p hg
    simpa only [d160171, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11551 (p : Pattern) (guard : d160172 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160172, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160172, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160171 p = 1 := by simpa only [d160172, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11550 p hg
    simpa only [d160172, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11552 (p : Pattern) (guard : d753 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d753, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5582 p hg
    simpa only [d753, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11553 (p : Pattern) (guard : d754 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11552 p hg
    simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11554 (p : Pattern) (guard : d160106 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11553 p hg
    simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11555 (p : Pattern) (guard : d160107 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160106 p = 1 := by simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11554 p hg
    simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11556 (p : Pattern) (guard : d160108 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160001 p = 1 := by simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11330 p hg
    simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160107 p = 1 := by simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11555 p hg
    simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11557 (p : Pattern) (guard : d160109 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160109, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160109, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160108 p = 1 := by simpa only [d160109, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11556 p hg
    simpa only [d160109, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11558 (p : Pattern) (guard : d160110 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160110, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160110, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160109 p = 1 := by simpa only [d160110, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11557 p hg
    simpa only [d160110, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11559 (p : Pattern) (guard : d160173 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160172 p = 1 := by simpa only [d160173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11551 p hg
    simpa only [d160173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160110 p = 1 := by simpa only [d160173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11558 p hg
    simpa only [d160173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11560 (p : Pattern) (guard : d160111 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160107 p = 1 := by simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11555 p hg
    simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11561 (p : Pattern) (guard : d160112 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160112, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160112, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160111 p = 1 := by simpa only [d160112, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11560 p hg
    simpa only [d160112, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11562 (p : Pattern) (guard : d160113 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160113, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160113, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160112 p = 1 := by simpa only [d160113, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11561 p hg
    simpa only [d160113, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11563 (p : Pattern) (guard : d160114 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160110 p = 1 := by simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11558 p hg
    simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160113 p = 1 := by simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11562 p hg
    simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11564 (p : Pattern) (guard : d160174 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160173 p = 1 := by simpa only [d160174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11559 p hg
    simpa only [d160174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160114 p = 1 := by simpa only [d160174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11563 p hg
    simpa only [d160174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11565 (p : Pattern) (guard : d160175 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160174 p = 1 := by simpa only [d160175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11564 p hg
    simpa only [d160175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11566 (p : Pattern) (guard : d160176 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160175 p = 1 := by simpa only [d160176, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11565 p hg
    simpa only [d160176, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160176, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160176, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11567 (p : Pattern) (guard : d160177 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160177, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160177, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160176 p = 1 := by simpa only [d160177, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11566 p hg
    simpa only [d160177, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11568 (p : Pattern) (guard : d160115 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160113 p = 1 := by simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11562 p hg
    simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11569 (p : Pattern) (guard : d160116 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160114 p = 1 := by simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11563 p hg
    simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160115 p = 1 := by simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11568 p hg
    simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11570 (p : Pattern) (guard : d160117 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160116 p = 1 := by simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11569 p hg
    simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11571 (p : Pattern) (guard : d160118 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160117 p = 1 := by simpa only [d160118, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11570 p hg
    simpa only [d160118, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160118, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160118, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11572 (p : Pattern) (guard : d160119 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160118 p = 1 := by simpa only [d160119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11571 p hg
    simpa only [d160119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11573 (p : Pattern) (guard : d160178 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160177 p = 1 := by simpa only [d160178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11567 p hg
    simpa only [d160178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160119 p = 1 := by simpa only [d160178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11572 p hg
    simpa only [d160178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11574 (p : Pattern) (guard : d160179 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160178 p = 1 := by simpa only [d160179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11573 p hg
    simpa only [d160179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11575 (p : Pattern) (guard : d160180 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160179 p = 1 := by simpa only [d160180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11574 p hg
    simpa only [d160180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11576 (p : Pattern) (guard : d160205 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160180 p = 1 := by simpa only [d160205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11575 p hg
    simpa only [d160205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11577 (p : Pattern) (guard : d160120 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160115 p = 1 := by simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11568 p hg
    simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11578 (p : Pattern) (guard : d160121 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160120 p = 1 := by simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11577 p hg
    simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11579 (p : Pattern) (guard : d160122 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160121 p = 1 := by simpa only [d160122, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11578 p hg
    simpa only [d160122, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160122, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160122, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11580 (p : Pattern) (guard : d160123 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160123, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160123, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160122 p = 1 := by simpa only [d160123, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11579 p hg
    simpa only [d160123, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11581 (p : Pattern) (guard : d160124 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160119 p = 1 := by simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11572 p hg
    simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160123 p = 1 := by simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11580 p hg
    simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11582 (p : Pattern) (guard : d160125 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160124 p = 1 := by simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11581 p hg
    simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11583 (p : Pattern) (guard : d160126 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160125 p = 1 := by simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11582 p hg
    simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11584 (p : Pattern) (guard : d160140 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160126 p = 1 := by simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11583 p hg
    simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11585 (p : Pattern) (guard : d160206 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160205 p = 1 := by simpa only [d160206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11576 p hg
    simpa only [d160206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160140 p = 1 := by simpa only [d160206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11584 p hg
    simpa only [d160206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11586 (p : Pattern) (guard : d160207 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160206 p = 1 := by simpa only [d160207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11585 p hg
    simpa only [d160207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11587 (p : Pattern) (guard : d160184 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160119 p = 1 := by simpa only [d160184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11572 p hg
    simpa only [d160184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11588 (p : Pattern) (guard : d160185 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160184 p = 1 := by simpa only [d160185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11587 p hg
    simpa only [d160185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11589 (p : Pattern) (guard : d160186 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160185 p = 1 := by simpa only [d160186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11588 p hg
    simpa only [d160186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11590 (p : Pattern) (guard : d160208 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160186 p = 1 := by simpa only [d160208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11589 p hg
    simpa only [d160208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11591 (p : Pattern) (guard : d160209 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160208 p = 1 := by simpa only [d160209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11590 p hg
    simpa only [d160209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11592 (p : Pattern) (guard : d160210 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160209 p = 1 := by simpa only [d160210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11591 p hg
    simpa only [d160210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11593 (p : Pattern) (guard : d160211 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160207 p = 1 := by simpa only [d160211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11586 p hg
    simpa only [d160211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160210 p = 1 := by simpa only [d160211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11592 p hg
    simpa only [d160211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11594 (p : Pattern) (guard : d160232 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160211 p = 1 := by simpa only [d160232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11593 p hg
    simpa only [d160232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11595 (p : Pattern) (guard : d160233 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160232 p = 1 := by simpa only [d160233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11594 p hg
    simpa only [d160233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11596 (p : Pattern) (guard : d160234 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160234, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160234, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160233 p = 1 := by simpa only [d160234, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11595 p hg
    simpa only [d160234, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11597 (p : Pattern) (guard : d160235 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160234 p = 1 := by simpa only [d160235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11596 p hg
    simpa only [d160235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11598 (p : Pattern) (guard : d160128 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160123 p = 1 := by simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11580 p hg
    simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11599 (p : Pattern) (guard : d160129 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160128 p = 1 := by simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11598 p hg
    simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11600 (p : Pattern) (guard : d160130 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160129 p = 1 := by simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11599 p hg
    simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11601 (p : Pattern) (guard : d160141 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160130 p = 1 := by simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11600 p hg
    simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11602 (p : Pattern) (guard : d160222 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160141 p = 1 := by simpa only [d160222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11601 p hg
    simpa only [d160222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11603 (p : Pattern) (guard : d160223 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160222 p = 1 := by simpa only [d160223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11602 p hg
    simpa only [d160223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11604 (p : Pattern) (guard : d160224 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160223 p = 1 := by simpa only [d160224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11603 p hg
    simpa only [d160224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11605 (p : Pattern) (guard : d160225 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160224 p = 1 := by simpa only [d160225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11604 p hg
    simpa only [d160225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11606 (p : Pattern) (guard : d160226 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160225 p = 1 := by simpa only [d160226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11605 p hg
    simpa only [d160226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11607 (p : Pattern) (guard : d160236 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160236, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160236, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160226 p = 1 := by simpa only [d160236, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11606 p hg
    simpa only [d160236, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11608 (p : Pattern) (guard : d160237 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160236 p = 1 := by simpa only [d160237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11607 p hg
    simpa only [d160237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11609 (p : Pattern) (guard : d160238 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160235 p = 1 := by simpa only [d160238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11597 p hg
    simpa only [d160238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160237 p = 1 := by simpa only [d160238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11608 p hg
    simpa only [d160238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11610 (p : Pattern) (guard : d160239 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160238 p = 1 := by simpa only [d160239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11609 p hg
    simpa only [d160239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11611 (p : Pattern) (guard : d160240 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160239 p = 1 := by simpa only [d160240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d160240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11612 (p : Pattern) (guard : d160241 p = 1) : d47768 p ≤ (-1 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160231 p = 1 := by simpa only [d160241, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11544 p hg
    simpa only [d160241, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160240 p = 1 := by simpa only [d160241, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d160241, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11613 (p : Pattern) (guard : d659 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d659, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d659, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d542 p = 1 := by simpa only [d659, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5285 p hg
    simpa only [d659, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11614 (p : Pattern) (guard : d660 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d659 p = 1 := by simpa only [d660, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11613 p hg
    simpa only [d660, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d543 p = 1 := by simpa only [d660, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5287 p hg
    simpa only [d660, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11615 (p : Pattern) (guard : d661 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d660 p = 1 := by simpa only [d661, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d661, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d661, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5305 p hg
    simpa only [d661, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11616 (p : Pattern) (guard : d662 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d661 p = 1 := by simpa only [d662, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d662, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d662, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d662, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11617 (p : Pattern) (guard : d160242 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d662 p = 1 := by simpa only [d160242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11616 p hg
    simpa only [d160242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11618 (p : Pattern) (guard : d160243 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160242 p = 1 := by simpa only [d160243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11617 p hg
    simpa only [d160243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11619 (p : Pattern) (guard : d160244 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160243 p = 1 := by simpa only [d160244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11618 p hg
    simpa only [d160244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160062 p = 1 := by simpa only [d160244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11371 p hg
    simpa only [d160244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11620 (p : Pattern) (guard : d160245 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160245, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160245, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160244 p = 1 := by simpa only [d160245, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11619 p hg
    simpa only [d160245, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11621 (p : Pattern) (guard : d160246 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160246, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160246, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160245 p = 1 := by simpa only [d160246, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11620 p hg
    simpa only [d160246, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11622 (p : Pattern) (guard : d971 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d971, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d971, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d750 p = 1 := by simpa only [d971, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d971, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11623 (p : Pattern) (guard : d972 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d971 p = 1 := by simpa only [d972, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11622 p hg
    simpa only [d972, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d751 p = 1 := by simpa only [d972, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d972, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11624 (p : Pattern) (guard : d973 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d972 p = 1 := by simpa only [d973, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11623 p hg
    simpa only [d973, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d973, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5707 p hg
    simpa only [d973, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11625 (p : Pattern) (guard : d974 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d973 p = 1 := by simpa only [d974, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11624 p hg
    simpa only [d974, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d974, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d974, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11626 (p : Pattern) (guard : d160247 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d974 p = 1 := by simpa only [d160247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11625 p hg
    simpa only [d160247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11627 (p : Pattern) (guard : d160248 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160247 p = 1 := by simpa only [d160248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11626 p hg
    simpa only [d160248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11628 (p : Pattern) (guard : d160249 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160062 p = 1 := by simpa only [d160249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11371 p hg
    simpa only [d160249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160248 p = 1 := by simpa only [d160249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11627 p hg
    simpa only [d160249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11629 (p : Pattern) (guard : d160250 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160250, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160250, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160249 p = 1 := by simpa only [d160250, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11628 p hg
    simpa only [d160250, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11630 (p : Pattern) (guard : d160251 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160251, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160251, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160250 p = 1 := by simpa only [d160251, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11629 p hg
    simpa only [d160251, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11631 (p : Pattern) (guard : d160252 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160246 p = 1 := by simpa only [d160252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11621 p hg
    simpa only [d160252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160251 p = 1 := by simpa only [d160252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11630 p hg
    simpa only [d160252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11632 (p : Pattern) (guard : d160253 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160248 p = 1 := by simpa only [d160253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11627 p hg
    simpa only [d160253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11633 (p : Pattern) (guard : d160254 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160254, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160254, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160253 p = 1 := by simpa only [d160254, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11632 p hg
    simpa only [d160254, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11634 (p : Pattern) (guard : d160255 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160255, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160255, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160254 p = 1 := by simpa only [d160255, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11633 p hg
    simpa only [d160255, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11635 (p : Pattern) (guard : d160256 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160251 p = 1 := by simpa only [d160256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11630 p hg
    simpa only [d160256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160255 p = 1 := by simpa only [d160256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11634 p hg
    simpa only [d160256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11636 (p : Pattern) (guard : d160257 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160252 p = 1 := by simpa only [d160257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11631 p hg
    simpa only [d160257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160256 p = 1 := by simpa only [d160257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11635 p hg
    simpa only [d160257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11637 (p : Pattern) (guard : d160258 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160257 p = 1 := by simpa only [d160258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11636 p hg
    simpa only [d160258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11638 (p : Pattern) (guard : d160259 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160258 p = 1 := by simpa only [d160259, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11637 p hg
    simpa only [d160259, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160259, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160259, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11639 (p : Pattern) (guard : d160260 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160260, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160260, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160259 p = 1 := by simpa only [d160260, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11638 p hg
    simpa only [d160260, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11640 (p : Pattern) (guard : d160261 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160255 p = 1 := by simpa only [d160261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11634 p hg
    simpa only [d160261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11641 (p : Pattern) (guard : d160262 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160256 p = 1 := by simpa only [d160262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11635 p hg
    simpa only [d160262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160261 p = 1 := by simpa only [d160262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d160262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11642 (p : Pattern) (guard : d160263 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160262 p = 1 := by simpa only [d160263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11641 p hg
    simpa only [d160263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11643 (p : Pattern) (guard : d160264 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160263 p = 1 := by simpa only [d160264, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11642 p hg
    simpa only [d160264, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160264, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160264, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11644 (p : Pattern) (guard : d160265 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160265, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160265, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160264 p = 1 := by simpa only [d160265, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11643 p hg
    simpa only [d160265, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11645 (p : Pattern) (guard : d160266 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160260 p = 1 := by simpa only [d160266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d160266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160265 p = 1 := by simpa only [d160266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11644 p hg
    simpa only [d160266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11646 (p : Pattern) (guard : d160267 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160266 p = 1 := by simpa only [d160267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11645 p hg
    simpa only [d160267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11647 (p : Pattern) (guard : d160268 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160267 p = 1 := by simpa only [d160268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11646 p hg
    simpa only [d160268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11648 (p : Pattern) (guard : d160269 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160268 p = 1 := by simpa only [d160269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11647 p hg
    simpa only [d160269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11649 (p : Pattern) (guard : d160270 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160261 p = 1 := by simpa only [d160270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d160270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11650 (p : Pattern) (guard : d160271 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160270 p = 1 := by simpa only [d160271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11649 p hg
    simpa only [d160271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11651 (p : Pattern) (guard : d160272 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160271 p = 1 := by simpa only [d160272, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11650 p hg
    simpa only [d160272, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160272, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160272, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11652 (p : Pattern) (guard : d160273 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160273, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160273, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160272 p = 1 := by simpa only [d160273, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11651 p hg
    simpa only [d160273, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11653 (p : Pattern) (guard : d160274 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160265 p = 1 := by simpa only [d160274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11644 p hg
    simpa only [d160274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160273 p = 1 := by simpa only [d160274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11652 p hg
    simpa only [d160274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11654 (p : Pattern) (guard : d160275 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160274 p = 1 := by simpa only [d160275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11653 p hg
    simpa only [d160275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11655 (p : Pattern) (guard : d160276 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160275 p = 1 := by simpa only [d160276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11654 p hg
    simpa only [d160276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11656 (p : Pattern) (guard : d160277 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160276 p = 1 := by simpa only [d160277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11655 p hg
    simpa only [d160277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11657 (p : Pattern) (guard : d160278 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160269 p = 1 := by simpa only [d160278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11648 p hg
    simpa only [d160278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160277 p = 1 := by simpa only [d160278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11656 p hg
    simpa only [d160278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11658 (p : Pattern) (guard : d160279 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160278 p = 1 := by simpa only [d160279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11657 p hg
    simpa only [d160279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11659 (p : Pattern) (guard : d160280 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160265 p = 1 := by simpa only [d160280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11644 p hg
    simpa only [d160280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11660 (p : Pattern) (guard : d160281 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160280 p = 1 := by simpa only [d160281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11659 p hg
    simpa only [d160281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11661 (p : Pattern) (guard : d160282 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160281 p = 1 := by simpa only [d160282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11660 p hg
    simpa only [d160282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11662 (p : Pattern) (guard : d160283 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160282 p = 1 := by simpa only [d160283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11661 p hg
    simpa only [d160283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11663 (p : Pattern) (guard : d160284 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160283 p = 1 := by simpa only [d160284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11662 p hg
    simpa only [d160284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11664 (p : Pattern) (guard : d160285 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160284 p = 1 := by simpa only [d160285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11663 p hg
    simpa only [d160285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11665 (p : Pattern) (guard : d160286 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160279 p = 1 := by simpa only [d160286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11658 p hg
    simpa only [d160286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160285 p = 1 := by simpa only [d160286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11664 p hg
    simpa only [d160286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11666 (p : Pattern) (guard : d160287 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160286 p = 1 := by simpa only [d160287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11665 p hg
    simpa only [d160287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11667 (p : Pattern) (guard : d160288 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160287 p = 1 := by simpa only [d160288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11666 p hg
    simpa only [d160288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11668 (p : Pattern) (guard : d160289 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160289, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160289, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160288 p = 1 := by simpa only [d160289, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11667 p hg
    simpa only [d160289, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11669 (p : Pattern) (guard : d160290 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160289 p = 1 := by simpa only [d160290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11668 p hg
    simpa only [d160290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11670 (p : Pattern) (guard : d160291 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160273 p = 1 := by simpa only [d160291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11652 p hg
    simpa only [d160291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11671 (p : Pattern) (guard : d160292 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160291 p = 1 := by simpa only [d160292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11670 p hg
    simpa only [d160292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11672 (p : Pattern) (guard : d160293 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160292 p = 1 := by simpa only [d160293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11671 p hg
    simpa only [d160293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11673 (p : Pattern) (guard : d160294 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160293 p = 1 := by simpa only [d160294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11672 p hg
    simpa only [d160294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11674 (p : Pattern) (guard : d160295 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160294 p = 1 := by simpa only [d160295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11673 p hg
    simpa only [d160295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11675 (p : Pattern) (guard : d160296 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160295 p = 1 := by simpa only [d160296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11674 p hg
    simpa only [d160296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11676 (p : Pattern) (guard : d160297 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160296 p = 1 := by simpa only [d160297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11675 p hg
    simpa only [d160297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11677 (p : Pattern) (guard : d160298 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160297 p = 1 := by simpa only [d160298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11676 p hg
    simpa only [d160298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11678 (p : Pattern) (guard : d160299 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160298 p = 1 := by simpa only [d160299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11677 p hg
    simpa only [d160299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11679 (p : Pattern) (guard : d160300 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160300, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160300, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160299 p = 1 := by simpa only [d160300, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11678 p hg
    simpa only [d160300, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11680 (p : Pattern) (guard : d160301 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160300 p = 1 := by simpa only [d160301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11679 p hg
    simpa only [d160301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11681 (p : Pattern) (guard : d160302 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160290 p = 1 := by simpa only [d160302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11669 p hg
    simpa only [d160302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160301 p = 1 := by simpa only [d160302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11680 p hg
    simpa only [d160302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11682 (p : Pattern) (guard : d160303 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160302 p = 1 := by simpa only [d160303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11681 p hg
    simpa only [d160303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11683 (p : Pattern) (guard : d160304 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160303 p = 1 := by simpa only [d160304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11682 p hg
    simpa only [d160304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11684 (p : Pattern) (guard : d160305 p = 1) : d47865 p ≤ (-1 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160304 p = 1 := by simpa only [d160305, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11683 p hg
    simpa only [d160305, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160305, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11105 p hg
    simpa only [d160305, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11685 (p : Pattern) (guard : d160306 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d160241 p = 1 := by simpa only [d160306, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11612 p hg
    simpa only [d160306, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160305 p = 1 := by simpa only [d160306, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11684 p hg
    simpa only [d160306, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11686 (p : Pattern) (guard : d160307 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160306 p = 1 := by simpa only [d160307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11685 p hg
    simpa only [d160307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11687 (p : Pattern) (guard : d160308 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160307 p = 1 := by simpa only [d160308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11686 p hg
    simpa only [d160308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11688 (p : Pattern) (guard : d160309 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160308 p = 1 := by simpa only [d160309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11687 p hg
    simpa only [d160309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11689 (p : Pattern) (guard : d160310 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160309 p = 1 := by simpa only [d160310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11688 p hg
    simpa only [d160310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11690 (p : Pattern) (guard : d160311 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160310 p = 1 := by simpa only [d160311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11689 p hg
    simpa only [d160311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11691 (p : Pattern) (guard : d160312 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160311 p = 1 := by simpa only [d160312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11690 p hg
    simpa only [d160312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11692 (p : Pattern) (guard : d160313 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160312 p = 1 := by simpa only [d160313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11691 p hg
    simpa only [d160313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11693 (p : Pattern) (guard : d160314 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d160105 p = 1 := by simpa only [d160314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11414 p hg
    simpa only [d160314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160313 p = 1 := by simpa only [d160314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11692 p hg
    simpa only [d160314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11694 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d1112, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5826 p hg
    simpa only [d1112, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11695 (p : Pattern) (guard : d1113 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11694 p hg
    simpa only [d1113, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d1113, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11696 (p : Pattern) (guard : d160315 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11695 p hg
    simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11697 (p : Pattern) (guard : d160316 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160315 p = 1 := by simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11696 p hg
    simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11698 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d1123, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5837 p hg
    simpa only [d1123, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11699 (p : Pattern) (guard : d1124 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11698 p hg
    simpa only [d1124, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d1124, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11700 (p : Pattern) (guard : d160317 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11699 p hg
    simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11701 (p : Pattern) (guard : d160318 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160317 p = 1 := by simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11700 p hg
    simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11702 (p : Pattern) (guard : d160319 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160316 p = 1 := by simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11697 p hg
    simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160318 p = 1 := by simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11701 p hg
    simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11703 (p : Pattern) (guard : d160320 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160320, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160320, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160319 p = 1 := by simpa only [d160320, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11702 p hg
    simpa only [d160320, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11704 (p : Pattern) (guard : d160321 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160321, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160321, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160320 p = 1 := by simpa only [d160321, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11703 p hg
    simpa only [d160321, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11705 (p : Pattern) (guard : d160322 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160318 p = 1 := by simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11701 p hg
    simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11706 (p : Pattern) (guard : d160323 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160323, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160323, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160322 p = 1 := by simpa only [d160323, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11705 p hg
    simpa only [d160323, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11707 (p : Pattern) (guard : d160324 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160324, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160324, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160323 p = 1 := by simpa only [d160324, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11706 p hg
    simpa only [d160324, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11708 (p : Pattern) (guard : d160325 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160321 p = 1 := by simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11704 p hg
    simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160324 p = 1 := by simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11707 p hg
    simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11709 (p : Pattern) (guard : d160326 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160324 p = 1 := by simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11707 p hg
    simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11710 (p : Pattern) (guard : d160327 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160325 p = 1 := by simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11708 p hg
    simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160326 p = 1 := by simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11709 p hg
    simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11711 (p : Pattern) (guard : d160328 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160327 p = 1 := by simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11710 p hg
    simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11712 (p : Pattern) (guard : d160329 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160328 p = 1 := by simpa only [d160329, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11711 p hg
    simpa only [d160329, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160329, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160329, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11713 (p : Pattern) (guard : d160330 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160330, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160330, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160329 p = 1 := by simpa only [d160330, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11712 p hg
    simpa only [d160330, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11714 (p : Pattern) (guard : d160331 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160326 p = 1 := by simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11709 p hg
    simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11715 (p : Pattern) (guard : d160332 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160331 p = 1 := by simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11714 p hg
    simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11716 (p : Pattern) (guard : d160333 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160332 p = 1 := by simpa only [d160333, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11715 p hg
    simpa only [d160333, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160333, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160333, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11717 (p : Pattern) (guard : d160334 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160334, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160334, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160333 p = 1 := by simpa only [d160334, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11716 p hg
    simpa only [d160334, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11718 (p : Pattern) (guard : d160335 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160330 p = 1 := by simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11713 p hg
    simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160334 p = 1 := by simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11717 p hg
    simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11719 (p : Pattern) (guard : d160336 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160335 p = 1 := by simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11718 p hg
    simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11720 (p : Pattern) (guard : d160337 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160336 p = 1 := by simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11719 p hg
    simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11721 (p : Pattern) (guard : d160338 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160337 p = 1 := by simpa only [d160338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11720 p hg
    simpa only [d160338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11722 (p : Pattern) (guard : d160339 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160334 p = 1 := by simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11717 p hg
    simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11723 (p : Pattern) (guard : d160340 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160339 p = 1 := by simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11722 p hg
    simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11724 (p : Pattern) (guard : d160341 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160340 p = 1 := by simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11723 p hg
    simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11725 (p : Pattern) (guard : d160342 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160341 p = 1 := by simpa only [d160342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11724 p hg
    simpa only [d160342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11726 (p : Pattern) (guard : d160343 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160338 p = 1 := by simpa only [d160343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11721 p hg
    simpa only [d160343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160342 p = 1 := by simpa only [d160343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11725 p hg
    simpa only [d160343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11727 (p : Pattern) (guard : d160344 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160343 p = 1 := by simpa only [d160344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11726 p hg
    simpa only [d160344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11728 (p : Pattern) (guard : d160345 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160344 p = 1 := by simpa only [d160345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11727 p hg
    simpa only [d160345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11729 (p : Pattern) (guard : d160346 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160345 p = 1 := by simpa only [d160346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11728 p hg
    simpa only [d160346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11730 (p : Pattern) (guard : d160347 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160346 p = 1 := by simpa only [d160347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11729 p hg
    simpa only [d160347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11731 (p : Pattern) (guard : d160348 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160347 p = 1 := by simpa only [d160348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11730 p hg
    simpa only [d160348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11732 (p : Pattern) (guard : d160349 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160348 p = 1 := by simpa only [d160349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11731 p hg
    simpa only [d160349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11733 (p : Pattern) (guard : d160350 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160349 p = 1 := by simpa only [d160350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11732 p hg
    simpa only [d160350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11734 (p : Pattern) (guard : d160351 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160337 p = 1 := by simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11720 p hg
    simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11735 (p : Pattern) (guard : d160352 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160341 p = 1 := by simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11724 p hg
    simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11736 (p : Pattern) (guard : d160353 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160351 p = 1 := by simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11734 p hg
    simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160352 p = 1 := by simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11735 p hg
    simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11737 (p : Pattern) (guard : d160354 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160353 p = 1 := by simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11736 p hg
    simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11738 (p : Pattern) (guard : d160355 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160354 p = 1 := by simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11737 p hg
    simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11739 (p : Pattern) (guard : d160356 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160355 p = 1 := by simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11738 p hg
    simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11740 (p : Pattern) (guard : d160357 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160356 p = 1 := by simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11739 p hg
    simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11741 (p : Pattern) (guard : d160358 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160347 p = 1 := by simpa only [d160358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11730 p hg
    simpa only [d160358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160357 p = 1 := by simpa only [d160358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11740 p hg
    simpa only [d160358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11742 (p : Pattern) (guard : d160359 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160348 p = 1 := by simpa only [d160359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11731 p hg
    simpa only [d160359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160358 p = 1 := by simpa only [d160359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11741 p hg
    simpa only [d160359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11743 (p : Pattern) (guard : d160360 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160359 p = 1 := by simpa only [d160360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11742 p hg
    simpa only [d160360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11744 (p : Pattern) (guard : d160361 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160350 p = 1 := by simpa only [d160361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11733 p hg
    simpa only [d160361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160360 p = 1 := by simpa only [d160361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11743 p hg
    simpa only [d160361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11745 (p : Pattern) (guard : d160362 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160336 p = 1 := by simpa only [d160362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11719 p hg
    simpa only [d160362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11746 (p : Pattern) (guard : d160363 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160362 p = 1 := by simpa only [d160363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11745 p hg
    simpa only [d160363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11747 (p : Pattern) (guard : d160364 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160340 p = 1 := by simpa only [d160364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11723 p hg
    simpa only [d160364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11748 (p : Pattern) (guard : d160365 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160364 p = 1 := by simpa only [d160365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11747 p hg
    simpa only [d160365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11749 (p : Pattern) (guard : d160366 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160363 p = 1 := by simpa only [d160366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11746 p hg
    simpa only [d160366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160365 p = 1 := by simpa only [d160366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11748 p hg
    simpa only [d160366, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
