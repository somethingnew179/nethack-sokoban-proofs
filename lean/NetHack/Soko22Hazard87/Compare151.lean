import NetHack.Soko22Hazard87.Compare150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37750 (p : Pattern) (guard : d318162 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318161 p = 1 := by simpa only [d318162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37749 p hg
    simpa only [d318162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37751 (p : Pattern) (guard : d318163 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318162 p = 1 := by simpa only [d318163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37750 p hg
    simpa only [d318163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37752 (p : Pattern) (guard : d318164 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318163 p = 1 := by simpa only [d318164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37751 p hg
    simpa only [d318164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37753 (p : Pattern) (guard : d318165 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318164 p = 1 := by simpa only [d318165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37752 p hg
    simpa only [d318165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37754 (p : Pattern) (guard : d318166 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d318166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318165 p = 1 := by simpa only [d318166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37753 p hg
    simpa only [d318166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37755 (p : Pattern) (guard : d318167 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318167, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318167, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318166 p = 1 := by simpa only [d318167, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37754 p hg
    simpa only [d318167, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37756 (p : Pattern) (guard : d318168 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d318168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318167 p = 1 := by simpa only [d318168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37755 p hg
    simpa only [d318168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37757 (p : Pattern) (guard : d318169 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318157 p = 1 := by simpa only [d318169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37745 p hg
    simpa only [d318169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318168 p = 1 := by simpa only [d318169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37756 p hg
    simpa only [d318169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37758 (p : Pattern) (guard : d318170 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318169 p = 1 := by simpa only [d318170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37757 p hg
    simpa only [d318170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d318170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37759 (p : Pattern) (guard : d318171 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318170 p = 1 := by simpa only [d318171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37758 p hg
    simpa only [d318171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d318171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37760 (p : Pattern) (guard : d318172 p = 1) : d50492 p ≤ (3 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318171 p = 1 := by simpa only [d318172, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37759 p hg
    simpa only [d318172, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318172, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d318172, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37761 (p : Pattern) (guard : d318173 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d318110 p = 1 := by simpa only [d318173, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37633 p hg
    simpa only [d318173, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318172 p = 1 := by simpa only [d318173, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37760 p hg
    simpa only [d318173, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37762 (p : Pattern) (guard : d318174 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318173 p = 1 := by simpa only [d318174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37761 p hg
    simpa only [d318174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37763 (p : Pattern) (guard : d318175 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318174 p = 1 := by simpa only [d318175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37762 p hg
    simpa only [d318175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37764 (p : Pattern) (guard : d318176 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318175 p = 1 := by simpa only [d318176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37763 p hg
    simpa only [d318176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37765 (p : Pattern) (guard : d318177 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318176 p = 1 := by simpa only [d318177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37764 p hg
    simpa only [d318177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37766 (p : Pattern) (guard : d318178 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318177 p = 1 := by simpa only [d318178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37765 p hg
    simpa only [d318178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37767 (p : Pattern) (guard : d318179 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318178 p = 1 := by simpa only [d318179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37766 p hg
    simpa only [d318179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37768 (p : Pattern) (guard : d318180 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318179 p = 1 := by simpa only [d318180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37767 p hg
    simpa only [d318180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37769 (p : Pattern) (guard : d318181 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318180 p = 1 := by simpa only [d318181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37768 p hg
    simpa only [d318181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37770 (p : Pattern) (guard : d318182 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318181 p = 1 := by simpa only [d318182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37769 p hg
    simpa only [d318182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37771 (p : Pattern) (guard : d318183 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318182 p = 1 := by simpa only [d318183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37770 p hg
    simpa only [d318183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37772 (p : Pattern) (guard : d318184 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d317975 p = 1 := by simpa only [d318184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37302 p hg
    simpa only [d318184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318183 p = 1 := by simpa only [d318184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37771 p hg
    simpa only [d318184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37773 (p : Pattern) (guard : d318185 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d318184 p = 1 := by simpa only [d318185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37772 p hg
    simpa only [d318185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37774 (p : Pattern) (guard : d318186 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d318185 p = 1 := by simpa only [d318186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37773 p hg
    simpa only [d318186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37775 (p : Pattern) (guard : d318187 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d318186 p = 1 := by simpa only [d318187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37774 p hg
    simpa only [d318187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37776 (p : Pattern) (guard : d318188 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d318187 p = 1 := by simpa only [d318188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37775 p hg
    simpa only [d318188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37777 (p : Pattern) (guard : d318189 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d318188 p = 1 := by simpa only [d318189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37776 p hg
    simpa only [d318189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37778 (p : Pattern) (guard : d318190 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d318189 p = 1 := by simpa only [d318190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37777 p hg
    simpa only [d318190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37779 (p : Pattern) (guard : d318191 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d318190 p = 1 := by simpa only [d318191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37778 p hg
    simpa only [d318191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37780 (p : Pattern) (guard : d318192 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d318191 p = 1 := by simpa only [d318192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37779 p hg
    simpa only [d318192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37781 (p : Pattern) (guard : d318193 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d318192 p = 1 := by simpa only [d318193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37780 p hg
    simpa only [d318193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37782 (p : Pattern) (guard : d318194 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d318193 p = 1 := by simpa only [d318194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37781 p hg
    simpa only [d318194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37783 (p : Pattern) (guard : d318195 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d318194 p = 1 := by simpa only [d318195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37782 p hg
    simpa only [d318195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37784 (p : Pattern) (guard : d318196 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d318195 p = 1 := by simpa only [d318196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37783 p hg
    simpa only [d318196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37785 (p : Pattern) (guard : d318197 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d318196 p = 1 := by simpa only [d318197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37784 p hg
    simpa only [d318197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37786 (p : Pattern) (guard : d318198 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d318197 p = 1 := by simpa only [d318198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37785 p hg
    simpa only [d318198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37787 (p : Pattern) (guard : d318199 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d318198 p = 1 := by simpa only [d318199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37786 p hg
    simpa only [d318199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37788 (p : Pattern) (guard : d318200 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d318199 p = 1 := by simpa only [d318200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37787 p hg
    simpa only [d318200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37789 (p : Pattern) (guard : d318201 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d318200 p = 1 := by simpa only [d318201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37788 p hg
    simpa only [d318201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37790 (p : Pattern) (guard : d318202 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d318201 p = 1 := by simpa only [d318202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37789 p hg
    simpa only [d318202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37791 (p : Pattern) (guard : d318203 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d318202 p = 1 := by simpa only [d318203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37790 p hg
    simpa only [d318203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37792 (p : Pattern) (guard : d318204 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d318203 p = 1 := by simpa only [d318204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37791 p hg
    simpa only [d318204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37793 (p : Pattern) (guard : d318205 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d318204 p = 1 := by simpa only [d318205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37792 p hg
    simpa only [d318205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37794 (p : Pattern) (guard : d318206 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d318205 p = 1 := by simpa only [d318206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37793 p hg
    simpa only [d318206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37795 (p : Pattern) (guard : d318207 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d318206 p = 1 := by simpa only [d318207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37794 p hg
    simpa only [d318207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37796 (p : Pattern) (guard : d318208 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d318207 p = 1 := by simpa only [d318208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37795 p hg
    simpa only [d318208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37797 (p : Pattern) (guard : d318209 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d318208 p = 1 := by simpa only [d318209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37796 p hg
    simpa only [d318209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37798 (p : Pattern) (guard : d318210 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d318209 p = 1 := by simpa only [d318210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37797 p hg
    simpa only [d318210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37799 (p : Pattern) (guard : d318211 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d318210 p = 1 := by simpa only [d318211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37798 p hg
    simpa only [d318211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37800 (p : Pattern) (guard : d318212 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d318211 p = 1 := by simpa only [d318212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37799 p hg
    simpa only [d318212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37801 (p : Pattern) (guard : d318213 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d318212 p = 1 := by simpa only [d318213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37800 p hg
    simpa only [d318213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37802 (p : Pattern) (guard : d318214 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d318213 p = 1 := by simpa only [d318214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37801 p hg
    simpa only [d318214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37803 (p : Pattern) (guard : d318215 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d318214 p = 1 := by simpa only [d318215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37802 p hg
    simpa only [d318215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37804 (p : Pattern) (guard : d318216 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d318215 p = 1 := by simpa only [d318216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37803 p hg
    simpa only [d318216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37805 (p : Pattern) (guard : d318217 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d318216 p = 1 := by simpa only [d318217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37804 p hg
    simpa only [d318217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37806 (p : Pattern) (guard : d318218 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d318217 p = 1 := by simpa only [d318218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37805 p hg
    simpa only [d318218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37807 (p : Pattern) (guard : d318219 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d318218 p = 1 := by simpa only [d318219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37806 p hg
    simpa only [d318219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37808 (p : Pattern) (guard : d318220 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d318219 p = 1 := by simpa only [d318220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37807 p hg
    simpa only [d318220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37809 (p : Pattern) (guard : d318221 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d318220 p = 1 := by simpa only [d318221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37808 p hg
    simpa only [d318221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37810 (p : Pattern) (guard : d318222 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d318221 p = 1 := by simpa only [d318222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37809 p hg
    simpa only [d318222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37811 (p : Pattern) (guard : d318223 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d318222 p = 1 := by simpa only [d318223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37810 p hg
    simpa only [d318223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37812 (p : Pattern) (guard : d318224 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d318223 p = 1 := by simpa only [d318224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37811 p hg
    simpa only [d318224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37813 (p : Pattern) (guard : d318225 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d318224 p = 1 := by simpa only [d318225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37812 p hg
    simpa only [d318225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37814 (p : Pattern) (guard : d318226 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d318225 p = 1 := by simpa only [d318226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37813 p hg
    simpa only [d318226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37815 (p : Pattern) (guard : d318227 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d318226 p = 1 := by simpa only [d318227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37814 p hg
    simpa only [d318227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d318227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37816 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37817 (p : Pattern) (guard : d0 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37818 (p : Pattern) (guard : d0 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37819 (p : Pattern) (guard : d0 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37820 (p : Pattern) (guard : d0 p = 1) : d50266 p ≤ (2 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37821 (p : Pattern) (guard : d0 p = 1) : d50270 p ≤ (2 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37822 (p : Pattern) (guard : d0 p = 1) : d50216 p ≤ (2 : Int) + d47681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37823 (p : Pattern) (guard : d0 p = 1) : d50219 p ≤ (2 : Int) + d47655 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37824 (p : Pattern) (guard : d0 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37825 (p : Pattern) (guard : d16 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare37826 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37827 (p : Pattern) (guard : d17 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37825 p hg
    simpa only [d17, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d17, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37828 (p : Pattern) (guard : d38813 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37827 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37829 (p : Pattern) (guard : d257183 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37828 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37830 (p : Pattern) (guard : d0 p = 1) : d50121 p ≤ (2 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37831 (p : Pattern) (guard : d257184 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37829 p hg
    simpa only [d257184, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d257184, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37832 (p : Pattern) (guard : d0 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37833 (p : Pattern) (guard : d257185 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37831 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37834 (p : Pattern) (guard : d257186 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257185 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37833 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37835 (p : Pattern) (guard : d0 p = 1) : d50201 p ≤ (2 : Int) + d47618 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37836 (p : Pattern) (guard : d257187 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257186 p = 1 := by simpa only [d257187, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37834 p hg
    simpa only [d257187, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257187, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d257187, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37837 (p : Pattern) (guard : d0 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37838 (p : Pattern) (guard : d257188 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257187 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37836 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37837 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37839 (p : Pattern) (guard : d0 p = 1) : d50180 p ≤ (2 : Int) + d47659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37840 (p : Pattern) (guard : d257189 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d257188 p = 1 := by simpa only [d257189, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37838 p hg
    simpa only [d257189, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257189, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d257189, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37841 (p : Pattern) (guard : d0 p = 1) : d50184 p ≤ (2 : Int) + d47662 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37842 (p : Pattern) (guard : d257190 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d257189 p = 1 := by simpa only [d257190, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37840 p hg
    simpa only [d257190, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257190, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d257190, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37843 (p : Pattern) (guard : d257191 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257191, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d257191, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257190 p = 1 := by simpa only [d257191, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37842 p hg
    simpa only [d257191, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37844 (p : Pattern) (guard : d0 p = 1) : d50225 p ≤ (2 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37845 (p : Pattern) (guard : d257192 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d257191 p = 1 := by simpa only [d257192, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37843 p hg
    simpa only [d257192, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257192, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d257192, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37846 (p : Pattern) (guard : d0 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37847 (p : Pattern) (guard : d257193 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d257192 p = 1 := by simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37845 p hg
    simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37848 (p : Pattern) (guard : d257194 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d257193 p = 1 := by simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37847 p hg
    simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37849 (p : Pattern) (guard : d257195 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d257194 p = 1 := by simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37848 p hg
    simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37850 (p : Pattern) (guard : d257196 p = 1) : d50227 p ≤ (2 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257196, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d257196, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257195 p = 1 := by simpa only [d257196, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37849 p hg
    simpa only [d257196, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37851 (p : Pattern) (guard : d257197 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257197, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d257197, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257196 p = 1 := by simpa only [d257197, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37850 p hg
    simpa only [d257197, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37852 (p : Pattern) (guard : d0 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37853 (p : Pattern) (guard : d257198 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d257197 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37851 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37854 (p : Pattern) (guard : d257199 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d257198 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37853 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37855 (p : Pattern) (guard : d257200 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d257199 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37854 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37856 (p : Pattern) (guard : d0 p = 1) : d50249 p ≤ (2 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37857 (p : Pattern) (guard : d257201 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d257200 p = 1 := by simpa only [d257201, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37855 p hg
    simpa only [d257201, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257201, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d257201, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37858 (p : Pattern) (guard : d257202 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257202, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d257202, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257201 p = 1 := by simpa only [d257202, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37857 p hg
    simpa only [d257202, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37859 (p : Pattern) (guard : d257203 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d257202 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37858 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37860 (p : Pattern) (guard : d257204 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d257203 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37859 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37861 (p : Pattern) (guard : d257205 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257204 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37860 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37862 (p : Pattern) (guard : d257206 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257205 p = 1 := by simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37861 p hg
    simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37863 (p : Pattern) (guard : d257207 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257206 p = 1 := by simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37862 p hg
    simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37864 (p : Pattern) (guard : d257265 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257207 p = 1 := by simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37863 p hg
    simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37865 (p : Pattern) (guard : d257266 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257265 p = 1 := by simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37864 p hg
    simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37866 (p : Pattern) (guard : d257267 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257266 p = 1 := by simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37865 p hg
    simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37867 (p : Pattern) (guard : d257268 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257267 p = 1 := by simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37866 p hg
    simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37868 (p : Pattern) (guard : d257269 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257269, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257269, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257268 p = 1 := by simpa only [d257269, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37867 p hg
    simpa only [d257269, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37869 (p : Pattern) (guard : d0 p = 1) : d50238 p ≤ (2 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37870 (p : Pattern) (guard : d0 p = 1) : d50247 p ≤ (2 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37871 (p : Pattern) (guard : d257197 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257197, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d257197, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257196 p = 1 := by simpa only [d257197, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37850 p hg
    simpa only [d257197, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37872 (p : Pattern) (guard : d0 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37873 (p : Pattern) (guard : d257198 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d257197 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37871 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37874 (p : Pattern) (guard : d257199 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d257198 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37873 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37875 (p : Pattern) (guard : d257200 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d257199 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37874 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37876 (p : Pattern) (guard : d257201 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d257200 p = 1 := by simpa only [d257201, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37875 p hg
    simpa only [d257201, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257201, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d257201, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37877 (p : Pattern) (guard : d257202 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257202, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d257202, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257201 p = 1 := by simpa only [d257202, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37876 p hg
    simpa only [d257202, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37878 (p : Pattern) (guard : d257203 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d257202 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37877 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37879 (p : Pattern) (guard : d257204 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d257203 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37878 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37880 (p : Pattern) (guard : d257205 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257204 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37879 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37881 (p : Pattern) (guard : d257206 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257205 p = 1 := by simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37880 p hg
    simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37882 (p : Pattern) (guard : d257207 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257206 p = 1 := by simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37881 p hg
    simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37883 (p : Pattern) (guard : d257265 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257207 p = 1 := by simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37882 p hg
    simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37884 (p : Pattern) (guard : d257266 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257265 p = 1 := by simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37883 p hg
    simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37885 (p : Pattern) (guard : d257267 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257266 p = 1 := by simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37884 p hg
    simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37886 (p : Pattern) (guard : d257268 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257267 p = 1 := by simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37885 p hg
    simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37887 (p : Pattern) (guard : d257213 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d257205 p = 1 := by simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37861 p hg
    simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37888 (p : Pattern) (guard : d257214 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257213 p = 1 := by simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37887 p hg
    simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37889 (p : Pattern) (guard : d257272 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257214 p = 1 := by simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37888 p hg
    simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37890 (p : Pattern) (guard : d257273 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257272 p = 1 := by simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37889 p hg
    simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37891 (p : Pattern) (guard : d257274 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257273 p = 1 := by simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37890 p hg
    simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37892 (p : Pattern) (guard : d257275 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257274 p = 1 := by simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37891 p hg
    simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37893 (p : Pattern) (guard : d257276 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d257268 p = 1 := by simpa only [d257276, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37886 p hg
    simpa only [d257276, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257275 p = 1 := by simpa only [d257276, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37892 p hg
    simpa only [d257276, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37894 (p : Pattern) (guard : d257277 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d257269 p = 1 := by simpa only [d257277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37868 p hg
    simpa only [d257277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257276 p = 1 := by simpa only [d257277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37893 p hg
    simpa only [d257277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37895 (p : Pattern) (guard : d257278 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d257277 p = 1 := by simpa only [d257278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37894 p hg
    simpa only [d257278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d257278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37896 (p : Pattern) (guard : d259883 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d257278 p = 1 := by simpa only [d259883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37895 p hg
    simpa only [d259883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d259883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37897 (p : Pattern) (guard : d259884 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d259884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259883 p = 1 := by simpa only [d259884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37896 p hg
    simpa only [d259884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37898 (p : Pattern) (guard : d0 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37899 (p : Pattern) (guard : d0 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37900 (p : Pattern) (guard : d0 p = 1) : d50376 p ≤ (2 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37901 (p : Pattern) (guard : d0 p = 1) : d50384 p ≤ (2 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37902 (p : Pattern) (guard : d0 p = 1) : d50358 p ≤ (2 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37903 (p : Pattern) (guard : d0 p = 1) : d50361 p ≤ (2 : Int) + d47734 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37904 (p : Pattern) (guard : d0 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37905 (p : Pattern) (guard : d16 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare37906 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37907 (p : Pattern) (guard : d17 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37905 p hg
    simpa only [d17, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d17, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37908 (p : Pattern) (guard : d38813 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37907 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37909 (p : Pattern) (guard : d257183 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37908 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37910 (p : Pattern) (guard : d0 p = 1) : d50290 p ≤ (2 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37911 (p : Pattern) (guard : d257184 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37909 p hg
    simpa only [d257184, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d257184, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37912 (p : Pattern) (guard : d0 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37913 (p : Pattern) (guard : d257185 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37911 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37914 (p : Pattern) (guard : d257186 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257185 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37913 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37915 (p : Pattern) (guard : d0 p = 1) : d50346 p ≤ (2 : Int) + d47707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37916 (p : Pattern) (guard : d257187 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257186 p = 1 := by simpa only [d257187, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37914 p hg
    simpa only [d257187, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257187, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d257187, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37917 (p : Pattern) (guard : d0 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37918 (p : Pattern) (guard : d257188 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257187 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37916 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37917 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37919 (p : Pattern) (guard : d0 p = 1) : d50183 p ≤ (2 : Int) + d47661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37920 (p : Pattern) (guard : d257189 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d257188 p = 1 := by simpa only [d257189, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37918 p hg
    simpa only [d257189, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257189, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d257189, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37921 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37922 (p : Pattern) (guard : d257190 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d257189 p = 1 := by simpa only [d257190, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37920 p hg
    simpa only [d257190, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257190, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d257190, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37923 (p : Pattern) (guard : d257191 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257191, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d257191, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257190 p = 1 := by simpa only [d257191, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37922 p hg
    simpa only [d257191, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37924 (p : Pattern) (guard : d0 p = 1) : d50367 p ≤ (2 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37925 (p : Pattern) (guard : d257192 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d257191 p = 1 := by simpa only [d257192, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37923 p hg
    simpa only [d257192, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257192, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d257192, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37926 (p : Pattern) (guard : d0 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37927 (p : Pattern) (guard : d257193 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d257192 p = 1 := by simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37925 p hg
    simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37928 (p : Pattern) (guard : d257194 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d257193 p = 1 := by simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37927 p hg
    simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37929 (p : Pattern) (guard : d257195 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d257194 p = 1 := by simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37928 p hg
    simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37930 (p : Pattern) (guard : d257196 p = 1) : d50369 p ≤ (2 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257196, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d257196, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257195 p = 1 := by simpa only [d257196, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37929 p hg
    simpa only [d257196, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37931 (p : Pattern) (guard : d257197 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257197, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d257197, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257196 p = 1 := by simpa only [d257197, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37930 p hg
    simpa only [d257197, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37932 (p : Pattern) (guard : d0 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37933 (p : Pattern) (guard : d257198 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d257197 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37931 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37934 (p : Pattern) (guard : d257199 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d257198 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37933 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37935 (p : Pattern) (guard : d257200 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d257199 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37934 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37936 (p : Pattern) (guard : d0 p = 1) : d50386 p ≤ (2 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37937 (p : Pattern) (guard : d257201 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d257200 p = 1 := by simpa only [d257201, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37935 p hg
    simpa only [d257201, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257201, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d257201, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37938 (p : Pattern) (guard : d257202 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257202, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d257202, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257201 p = 1 := by simpa only [d257202, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37937 p hg
    simpa only [d257202, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37939 (p : Pattern) (guard : d257203 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d257202 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37938 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37940 (p : Pattern) (guard : d257204 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d257203 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37939 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37941 (p : Pattern) (guard : d257205 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257204 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37940 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37942 (p : Pattern) (guard : d257213 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d257205 p = 1 := by simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37941 p hg
    simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37943 (p : Pattern) (guard : d257214 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257213 p = 1 := by simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37942 p hg
    simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37944 (p : Pattern) (guard : d257272 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257214 p = 1 := by simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37943 p hg
    simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37945 (p : Pattern) (guard : d257273 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257272 p = 1 := by simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37944 p hg
    simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37946 (p : Pattern) (guard : d257274 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257273 p = 1 := by simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37945 p hg
    simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37947 (p : Pattern) (guard : d257275 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257274 p = 1 := by simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37946 p hg
    simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37948 (p : Pattern) (guard : d257490 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257490, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257490, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257275 p = 1 := by simpa only [d257490, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37947 p hg
    simpa only [d257490, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37949 (p : Pattern) (guard : d257491 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d257491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257490 p = 1 := by simpa only [d257491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37948 p hg
    simpa only [d257491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37950 (p : Pattern) (guard : d259885 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d257491 p = 1 := by simpa only [d259885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37949 p hg
    simpa only [d259885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d259885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37951 (p : Pattern) (guard : d259886 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259885 p = 1 := by simpa only [d259886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37950 p hg
    simpa only [d259886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d259886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37952 (p : Pattern) (guard : d259887 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259886 p = 1 := by simpa only [d259887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37951 p hg
    simpa only [d259887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d259887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37953 (p : Pattern) (guard : d259888 p = 1) : d50390 p ≤ (2 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259884 p = 1 := by simpa only [d259888, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37897 p hg
    simpa only [d259888, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259887 p = 1 := by simpa only [d259888, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37952 p hg
    simpa only [d259888, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37954 (p : Pattern) (guard : d0 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37955 (p : Pattern) (guard : d0 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37956 (p : Pattern) (guard : d0 p = 1) : d50408 p ≤ (2 : Int) + d47786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37957 (p : Pattern) (guard : d0 p = 1) : d50419 p ≤ (2 : Int) + d47796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37958 (p : Pattern) (guard : d0 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37959 (p : Pattern) (guard : d0 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37960 (p : Pattern) (guard : d16 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare37961 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37962 (p : Pattern) (guard : d17 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37960 p hg
    simpa only [d17, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d17, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37963 (p : Pattern) (guard : d38813 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37962 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37964 (p : Pattern) (guard : d257183 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37963 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37965 (p : Pattern) (guard : d0 p = 1) : d50141 p ≤ (2 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37966 (p : Pattern) (guard : d257184 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37964 p hg
    simpa only [d257184, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d257184, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37967 (p : Pattern) (guard : d0 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37968 (p : Pattern) (guard : d257185 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37966 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37969 (p : Pattern) (guard : d257186 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257185 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37968 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37970 (p : Pattern) (guard : d0 p = 1) : d50142 p ≤ (2 : Int) + d47631 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37971 (p : Pattern) (guard : d257187 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257186 p = 1 := by simpa only [d257187, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37969 p hg
    simpa only [d257187, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257187, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d257187, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37972 (p : Pattern) (guard : d257188 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257187 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37971 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37973 (p : Pattern) (guard : d257230 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d257230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257188 p = 1 := by simpa only [d257230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37972 p hg
    simpa only [d257230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37974 (p : Pattern) (guard : d257189 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d257188 p = 1 := by simpa only [d257189, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37838 p hg
    simpa only [d257189, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257189, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d257189, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37975 (p : Pattern) (guard : d257231 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d257230 p = 1 := by simpa only [d257231, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37973 p hg
    simpa only [d257231, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257189 p = 1 := by simpa only [d257231, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37974 p hg
    simpa only [d257231, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37976 (p : Pattern) (guard : d0 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37977 (p : Pattern) (guard : d16 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare37978 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37979 (p : Pattern) (guard : d17 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37977 p hg
    simpa only [d17, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d17, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37980 (p : Pattern) (guard : d38813 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37979 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37981 (p : Pattern) (guard : d257183 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37980 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37982 (p : Pattern) (guard : d0 p = 1) : d50146 p ≤ (2 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37983 (p : Pattern) (guard : d257184 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37981 p hg
    simpa only [d257184, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d257184, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37984 (p : Pattern) (guard : d0 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37985 (p : Pattern) (guard : d257185 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37983 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37986 (p : Pattern) (guard : d257186 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257185 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37985 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37987 (p : Pattern) (guard : d0 p = 1) : d50147 p ≤ (2 : Int) + d47635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37988 (p : Pattern) (guard : d257187 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257186 p = 1 := by simpa only [d257187, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37986 p hg
    simpa only [d257187, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257187, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d257187, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37989 (p : Pattern) (guard : d0 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37990 (p : Pattern) (guard : d257188 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257187 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37988 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37989 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37991 (p : Pattern) (guard : d257189 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d257188 p = 1 := by simpa only [d257189, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37990 p hg
    simpa only [d257189, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257189, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d257189, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37992 (p : Pattern) (guard : d257190 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d257189 p = 1 := by simpa only [d257190, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37991 p hg
    simpa only [d257190, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257190, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d257190, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37993 (p : Pattern) (guard : d257232 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d257231 p = 1 := by simpa only [d257232, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37975 p hg
    simpa only [d257232, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257190 p = 1 := by simpa only [d257232, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37992 p hg
    simpa only [d257232, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37994 (p : Pattern) (guard : d0 p = 1) : d50425 p ≤ (2 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37995 (p : Pattern) (guard : d257233 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d257232 p = 1 := by simpa only [d257233, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37993 p hg
    simpa only [d257233, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257233, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d257233, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37996 (p : Pattern) (guard : d0 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37997 (p : Pattern) (guard : d257234 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d257233 p = 1 := by simpa only [d257234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37995 p hg
    simpa only [d257234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d257234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37998 (p : Pattern) (guard : d257235 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d257234 p = 1 := by simpa only [d257235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37997 p hg
    simpa only [d257235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d257235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37999 (p : Pattern) (guard : d257236 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d257235 p = 1 := by simpa only [d257236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37998 p hg
    simpa only [d257236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d257236, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
