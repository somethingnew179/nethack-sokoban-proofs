import NetHack.Soko22Hazard87.Compare086
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21750 (p : Pattern) (guard : d179171 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179170 p = 1 := by simpa only [d179171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21749 p hg
    simpa only [d179171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21751 (p : Pattern) (guard : d179172 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179171 p = 1 := by simpa only [d179172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21750 p hg
    simpa only [d179172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21752 (p : Pattern) (guard : d179173 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179172 p = 1 := by simpa only [d179173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21751 p hg
    simpa only [d179173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21753 (p : Pattern) (guard : d179174 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179173 p = 1 := by simpa only [d179174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21752 p hg
    simpa only [d179174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21754 (p : Pattern) (guard : d179175 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179174 p = 1 := by simpa only [d179175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21753 p hg
    simpa only [d179175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21755 (p : Pattern) (guard : d179176 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179175 p = 1 := by simpa only [d179176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21754 p hg
    simpa only [d179176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21756 (p : Pattern) (guard : d179177 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179122 p = 1 := by simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21642 p hg
    simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21757 (p : Pattern) (guard : d179178 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179177 p = 1 := by simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21756 p hg
    simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21758 (p : Pattern) (guard : d179179 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179178 p = 1 := by simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21757 p hg
    simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21759 (p : Pattern) (guard : d179180 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179179 p = 1 := by simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21758 p hg
    simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21760 (p : Pattern) (guard : d179181 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179181, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179181, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179180 p = 1 := by simpa only [d179181, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21759 p hg
    simpa only [d179181, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21761 (p : Pattern) (guard : d179182 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179181 p = 1 := by simpa only [d179182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21760 p hg
    simpa only [d179182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21762 (p : Pattern) (guard : d179183 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179182 p = 1 := by simpa only [d179183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21761 p hg
    simpa only [d179183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21763 (p : Pattern) (guard : d179177 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179122 p = 1 := by simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21661 p hg
    simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21764 (p : Pattern) (guard : d179178 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179177 p = 1 := by simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21763 p hg
    simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21765 (p : Pattern) (guard : d179179 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179178 p = 1 := by simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21764 p hg
    simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21766 (p : Pattern) (guard : d179180 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179179 p = 1 := by simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21765 p hg
    simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21767 (p : Pattern) (guard : d179184 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179129 p = 1 := by simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21667 p hg
    simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21768 (p : Pattern) (guard : d179185 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179184 p = 1 := by simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21767 p hg
    simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21769 (p : Pattern) (guard : d179186 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179185 p = 1 := by simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21768 p hg
    simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21770 (p : Pattern) (guard : d179187 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179186 p = 1 := by simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21769 p hg
    simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21771 (p : Pattern) (guard : d179188 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179180 p = 1 := by simpa only [d179188, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21766 p hg
    simpa only [d179188, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179187 p = 1 := by simpa only [d179188, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21770 p hg
    simpa only [d179188, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21772 (p : Pattern) (guard : d179189 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179181 p = 1 := by simpa only [d179189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21760 p hg
    simpa only [d179189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179188 p = 1 := by simpa only [d179189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21771 p hg
    simpa only [d179189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21773 (p : Pattern) (guard : d179190 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179189 p = 1 := by simpa only [d179190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21772 p hg
    simpa only [d179190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21774 (p : Pattern) (guard : d179191 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179183 p = 1 := by simpa only [d179191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21762 p hg
    simpa only [d179191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179190 p = 1 := by simpa only [d179191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21773 p hg
    simpa only [d179191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21775 (p : Pattern) (guard : d179192 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179119 p = 1 := by simpa only [d179192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21639 p hg
    simpa only [d179192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21776 (p : Pattern) (guard : d179193 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179192 p = 1 := by simpa only [d179193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21775 p hg
    simpa only [d179193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21777 (p : Pattern) (guard : d179194 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179193 p = 1 := by simpa only [d179194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21776 p hg
    simpa only [d179194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21778 (p : Pattern) (guard : d179195 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179194 p = 1 := by simpa only [d179195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21777 p hg
    simpa only [d179195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21779 (p : Pattern) (guard : d179196 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179195 p = 1 := by simpa only [d179196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21778 p hg
    simpa only [d179196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21780 (p : Pattern) (guard : d179197 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179196 p = 1 := by simpa only [d179197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21779 p hg
    simpa only [d179197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21781 (p : Pattern) (guard : d179198 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179118 p = 1 := by simpa only [d179198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21638 p hg
    simpa only [d179198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21782 (p : Pattern) (guard : d179199 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179198 p = 1 := by simpa only [d179199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21781 p hg
    simpa only [d179199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21783 (p : Pattern) (guard : d179200 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179199 p = 1 := by simpa only [d179200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21782 p hg
    simpa only [d179200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21784 (p : Pattern) (guard : d179201 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179200 p = 1 := by simpa only [d179201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21783 p hg
    simpa only [d179201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21785 (p : Pattern) (guard : d179202 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179201 p = 1 := by simpa only [d179202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21784 p hg
    simpa only [d179202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21786 (p : Pattern) (guard : d179203 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179202 p = 1 := by simpa only [d179203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21785 p hg
    simpa only [d179203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21787 (p : Pattern) (guard : d179211 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare21788 (p : Pattern) (guard : d179212 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179211 p = 1 := by simpa only [d179212, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21787 p hg
    simpa only [d179212, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179212, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179212, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21789 (p : Pattern) (guard : d179213 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179212 p = 1 := by simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21788 p hg
    simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21790 (p : Pattern) (guard : d179214 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179213 p = 1 := by simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21789 p hg
    simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21791 (p : Pattern) (guard : d179215 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179214 p = 1 := by simpa only [d179215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21790 p hg
    simpa only [d179215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179109 p = 1 := by simpa only [d179215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21627 p hg
    simpa only [d179215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21792 (p : Pattern) (guard : d179216 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179216, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179216, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179215 p = 1 := by simpa only [d179216, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21791 p hg
    simpa only [d179216, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21793 (p : Pattern) (guard : d179217 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179217, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179217, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179216 p = 1 := by simpa only [d179217, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21792 p hg
    simpa only [d179217, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21794 (p : Pattern) (guard : d179218 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179217 p = 1 := by simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21793 p hg
    simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179112 p = 1 := by simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21630 p hg
    simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21795 (p : Pattern) (guard : d179219 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179218 p = 1 := by simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21794 p hg
    simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179113 p = 1 := by simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21632 p hg
    simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21796 (p : Pattern) (guard : d179220 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179219 p = 1 := by simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21795 p hg
    simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21797 (p : Pattern) (guard : d179221 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179220 p = 1 := by simpa only [d179221, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21796 p hg
    simpa only [d179221, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179221, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179221, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21798 (p : Pattern) (guard : d179222 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179222, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179222, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179221 p = 1 := by simpa only [d179222, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21797 p hg
    simpa only [d179222, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21799 (p : Pattern) (guard : d179223 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179222 p = 1 := by simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21798 p hg
    simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179117 p = 1 := by simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21637 p hg
    simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21800 (p : Pattern) (guard : d179224 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179223 p = 1 := by simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21799 p hg
    simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21801 (p : Pattern) (guard : d179225 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179224 p = 1 := by simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21800 p hg
    simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21802 (p : Pattern) (guard : d179226 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179225 p = 1 := by simpa only [d179226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21801 p hg
    simpa only [d179226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21803 (p : Pattern) (guard : d179227 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179226 p = 1 := by simpa only [d179227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21802 p hg
    simpa only [d179227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179121 p = 1 := by simpa only [d179227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21641 p hg
    simpa only [d179227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21804 (p : Pattern) (guard : d179228 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179227 p = 1 := by simpa only [d179228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21803 p hg
    simpa only [d179228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21805 (p : Pattern) (guard : d179229 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179228 p = 1 := by simpa only [d179229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21804 p hg
    simpa only [d179229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179123 p = 1 := by simpa only [d179229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21643 p hg
    simpa only [d179229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21806 (p : Pattern) (guard : d179230 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179203 p = 1 := by simpa only [d179230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21786 p hg
    simpa only [d179230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179229 p = 1 := by simpa only [d179230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21805 p hg
    simpa only [d179230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21807 (p : Pattern) (guard : d179231 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179197 p = 1 := by simpa only [d179231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21780 p hg
    simpa only [d179231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179230 p = 1 := by simpa only [d179231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21806 p hg
    simpa only [d179231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21808 (p : Pattern) (guard : d179232 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179232, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179232, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179231 p = 1 := by simpa only [d179232, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21807 p hg
    simpa only [d179232, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21809 (p : Pattern) (guard : d179192 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179119 p = 1 := by simpa only [d179192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21658 p hg
    simpa only [d179192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21810 (p : Pattern) (guard : d179193 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179192 p = 1 := by simpa only [d179193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21809 p hg
    simpa only [d179193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21811 (p : Pattern) (guard : d179194 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179193 p = 1 := by simpa only [d179194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21810 p hg
    simpa only [d179194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21812 (p : Pattern) (guard : d179195 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179194 p = 1 := by simpa only [d179195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21811 p hg
    simpa only [d179195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21813 (p : Pattern) (guard : d179196 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179195 p = 1 := by simpa only [d179196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21812 p hg
    simpa only [d179196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21814 (p : Pattern) (guard : d179197 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179196 p = 1 := by simpa only [d179197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21813 p hg
    simpa only [d179197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21815 (p : Pattern) (guard : d179198 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179118 p = 1 := by simpa only [d179198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21657 p hg
    simpa only [d179198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21816 (p : Pattern) (guard : d179199 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179198 p = 1 := by simpa only [d179199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21815 p hg
    simpa only [d179199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21817 (p : Pattern) (guard : d179200 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179199 p = 1 := by simpa only [d179200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21816 p hg
    simpa only [d179200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21818 (p : Pattern) (guard : d179201 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179200 p = 1 := by simpa only [d179201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21817 p hg
    simpa only [d179201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21819 (p : Pattern) (guard : d179202 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179201 p = 1 := by simpa only [d179202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21818 p hg
    simpa only [d179202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21820 (p : Pattern) (guard : d179203 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179202 p = 1 := by simpa only [d179203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21819 p hg
    simpa only [d179203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21821 (p : Pattern) (guard : d179217 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179217, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179217, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179216 p = 1 := by simpa only [d179217, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21792 p hg
    simpa only [d179217, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21822 (p : Pattern) (guard : d179218 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179217 p = 1 := by simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21821 p hg
    simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179112 p = 1 := by simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21650 p hg
    simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21823 (p : Pattern) (guard : d179219 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179218 p = 1 := by simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21822 p hg
    simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179113 p = 1 := by simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21652 p hg
    simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21824 (p : Pattern) (guard : d179220 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179219 p = 1 := by simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21823 p hg
    simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21825 (p : Pattern) (guard : d179221 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179220 p = 1 := by simpa only [d179221, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21824 p hg
    simpa only [d179221, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179221, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179221, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21826 (p : Pattern) (guard : d179222 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179222, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179222, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179221 p = 1 := by simpa only [d179222, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21825 p hg
    simpa only [d179222, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21827 (p : Pattern) (guard : d179223 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179222 p = 1 := by simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21826 p hg
    simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179117 p = 1 := by simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21656 p hg
    simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21828 (p : Pattern) (guard : d179224 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179223 p = 1 := by simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21827 p hg
    simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21829 (p : Pattern) (guard : d179225 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179224 p = 1 := by simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21828 p hg
    simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21830 (p : Pattern) (guard : d179226 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179225 p = 1 := by simpa only [d179226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21829 p hg
    simpa only [d179226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21831 (p : Pattern) (guard : d179227 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179226 p = 1 := by simpa only [d179227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21830 p hg
    simpa only [d179227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179121 p = 1 := by simpa only [d179227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21660 p hg
    simpa only [d179227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21832 (p : Pattern) (guard : d179228 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179227 p = 1 := by simpa only [d179228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21831 p hg
    simpa only [d179228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21833 (p : Pattern) (guard : d179229 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179228 p = 1 := by simpa only [d179229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21832 p hg
    simpa only [d179229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179123 p = 1 := by simpa only [d179229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21662 p hg
    simpa only [d179229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21834 (p : Pattern) (guard : d179230 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179203 p = 1 := by simpa only [d179230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21820 p hg
    simpa only [d179230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179229 p = 1 := by simpa only [d179230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21833 p hg
    simpa only [d179230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21835 (p : Pattern) (guard : d179231 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179197 p = 1 := by simpa only [d179231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21814 p hg
    simpa only [d179231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179230 p = 1 := by simpa only [d179231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21834 p hg
    simpa only [d179231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21836 (p : Pattern) (guard : d179233 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179192 p = 1 := by simpa only [d179233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21775 p hg
    simpa only [d179233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21837 (p : Pattern) (guard : d179234 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179233 p = 1 := by simpa only [d179234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21836 p hg
    simpa only [d179234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21838 (p : Pattern) (guard : d179235 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179234 p = 1 := by simpa only [d179235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21837 p hg
    simpa only [d179235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21839 (p : Pattern) (guard : d179236 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179235 p = 1 := by simpa only [d179236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21838 p hg
    simpa only [d179236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21840 (p : Pattern) (guard : d179237 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179236 p = 1 := by simpa only [d179237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21839 p hg
    simpa only [d179237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21841 (p : Pattern) (guard : d179238 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179199 p = 1 := by simpa only [d179238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21782 p hg
    simpa only [d179238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21842 (p : Pattern) (guard : d179239 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179238 p = 1 := by simpa only [d179239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21841 p hg
    simpa only [d179239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21843 (p : Pattern) (guard : d179240 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179239 p = 1 := by simpa only [d179240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21842 p hg
    simpa only [d179240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21844 (p : Pattern) (guard : d179241 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179240 p = 1 := by simpa only [d179241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21843 p hg
    simpa only [d179241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21845 (p : Pattern) (guard : d179242 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179225 p = 1 := by simpa only [d179242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21801 p hg
    simpa only [d179242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21846 (p : Pattern) (guard : d179243 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179242 p = 1 := by simpa only [d179243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21845 p hg
    simpa only [d179243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179128 p = 1 := by simpa only [d179243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21666 p hg
    simpa only [d179243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21847 (p : Pattern) (guard : d179244 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179243 p = 1 := by simpa only [d179244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21846 p hg
    simpa only [d179244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21848 (p : Pattern) (guard : d179245 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179244 p = 1 := by simpa only [d179245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21847 p hg
    simpa only [d179245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179130 p = 1 := by simpa only [d179245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21668 p hg
    simpa only [d179245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21849 (p : Pattern) (guard : d179246 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179241 p = 1 := by simpa only [d179246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21844 p hg
    simpa only [d179246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179245 p = 1 := by simpa only [d179246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21848 p hg
    simpa only [d179246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21850 (p : Pattern) (guard : d179247 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179237 p = 1 := by simpa only [d179247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21840 p hg
    simpa only [d179247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179246 p = 1 := by simpa only [d179247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21849 p hg
    simpa only [d179247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21851 (p : Pattern) (guard : d179248 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179231 p = 1 := by simpa only [d179248, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21835 p hg
    simpa only [d179248, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179247 p = 1 := by simpa only [d179248, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21850 p hg
    simpa only [d179248, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21852 (p : Pattern) (guard : d179249 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179232 p = 1 := by simpa only [d179249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21808 p hg
    simpa only [d179249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179248 p = 1 := by simpa only [d179249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21851 p hg
    simpa only [d179249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21853 (p : Pattern) (guard : d179250 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179180 p = 1 := by simpa only [d179250, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21766 p hg
    simpa only [d179250, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179250, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179250, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21854 (p : Pattern) (guard : d179251 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179250 p = 1 := by simpa only [d179251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21853 p hg
    simpa only [d179251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21855 (p : Pattern) (guard : d179252 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179249 p = 1 := by simpa only [d179252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21852 p hg
    simpa only [d179252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179251 p = 1 := by simpa only [d179252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21854 p hg
    simpa only [d179252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21856 (p : Pattern) (guard : d179253 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179252 p = 1 := by simpa only [d179253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21855 p hg
    simpa only [d179253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21857 (p : Pattern) (guard : d179254 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179191 p = 1 := by simpa only [d179254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21774 p hg
    simpa only [d179254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179253 p = 1 := by simpa only [d179254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21856 p hg
    simpa only [d179254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21858 (p : Pattern) (guard : d179211 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare21859 (p : Pattern) (guard : d179212 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179211 p = 1 := by simpa only [d179212, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21858 p hg
    simpa only [d179212, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179212, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179212, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21860 (p : Pattern) (guard : d179213 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179212 p = 1 := by simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21859 p hg
    simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21861 (p : Pattern) (guard : d179214 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179213 p = 1 := by simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21860 p hg
    simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21862 (p : Pattern) (guard : d179215 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179214 p = 1 := by simpa only [d179215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21861 p hg
    simpa only [d179215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179109 p = 1 := by simpa only [d179215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21687 p hg
    simpa only [d179215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21863 (p : Pattern) (guard : d179216 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179216, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179216, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179215 p = 1 := by simpa only [d179216, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21862 p hg
    simpa only [d179216, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21864 (p : Pattern) (guard : d179217 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179217, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179217, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179216 p = 1 := by simpa only [d179217, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21863 p hg
    simpa only [d179217, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21865 (p : Pattern) (guard : d179218 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179217 p = 1 := by simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21864 p hg
    simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179112 p = 1 := by simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21690 p hg
    simpa only [d179218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21866 (p : Pattern) (guard : d179219 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179218 p = 1 := by simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21865 p hg
    simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179113 p = 1 := by simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21692 p hg
    simpa only [d179219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21867 (p : Pattern) (guard : d179220 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179219 p = 1 := by simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21866 p hg
    simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21868 (p : Pattern) (guard : d179221 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179220 p = 1 := by simpa only [d179221, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21867 p hg
    simpa only [d179221, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179221, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179221, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21869 (p : Pattern) (guard : d179222 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179222, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179222, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179221 p = 1 := by simpa only [d179222, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21868 p hg
    simpa only [d179222, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21870 (p : Pattern) (guard : d179223 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179222 p = 1 := by simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21869 p hg
    simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179117 p = 1 := by simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21697 p hg
    simpa only [d179223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21871 (p : Pattern) (guard : d179224 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179223 p = 1 := by simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21870 p hg
    simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21872 (p : Pattern) (guard : d179225 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179224 p = 1 := by simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21871 p hg
    simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21873 (p : Pattern) (guard : d179242 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179225 p = 1 := by simpa only [d179242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21872 p hg
    simpa only [d179242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21874 (p : Pattern) (guard : d179243 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179242 p = 1 := by simpa only [d179243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21873 p hg
    simpa only [d179243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179128 p = 1 := by simpa only [d179243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21701 p hg
    simpa only [d179243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21875 (p : Pattern) (guard : d179244 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179243 p = 1 := by simpa only [d179244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21874 p hg
    simpa only [d179244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21876 (p : Pattern) (guard : d179245 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179244 p = 1 := by simpa only [d179245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21875 p hg
    simpa only [d179245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179130 p = 1 := by simpa only [d179245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21703 p hg
    simpa only [d179245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21877 (p : Pattern) (guard : d179255 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179245 p = 1 := by simpa only [d179255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21876 p hg
    simpa only [d179255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21878 (p : Pattern) (guard : d179256 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179255 p = 1 := by simpa only [d179256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21877 p hg
    simpa only [d179256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21879 (p : Pattern) (guard : d179257 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179257, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179257, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179256 p = 1 := by simpa only [d179257, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21878 p hg
    simpa only [d179257, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21880 (p : Pattern) (guard : d179258 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179257 p = 1 := by simpa only [d179258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21879 p hg
    simpa only [d179258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21881 (p : Pattern) (guard : d179259 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179258 p = 1 := by simpa only [d179259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21880 p hg
    simpa only [d179259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21882 (p : Pattern) (guard : d179260 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179259 p = 1 := by simpa only [d179260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21881 p hg
    simpa only [d179260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21883 (p : Pattern) (guard : d179261 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179260 p = 1 := by simpa only [d179261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21882 p hg
    simpa only [d179261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21884 (p : Pattern) (guard : d179262 p = 1) : d48359 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179254 p = 1 := by simpa only [d179262, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21857 p hg
    simpa only [d179262, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179261 p = 1 := by simpa only [d179262, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21883 p hg
    simpa only [d179262, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21885 (p : Pattern) (guard : d179265 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare21886 (p : Pattern) (guard : d179266 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179265 p = 1 := by simpa only [d179266, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21885 p hg
    simpa only [d179266, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179266, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d179266, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21887 (p : Pattern) (guard : d179267 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179266 p = 1 := by simpa only [d179267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21886 p hg
    simpa only [d179267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21888 (p : Pattern) (guard : d179268 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179267 p = 1 := by simpa only [d179268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21887 p hg
    simpa only [d179268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21889 (p : Pattern) (guard : d179269 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179268 p = 1 := by simpa only [d179269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21888 p hg
    simpa only [d179269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179146 p = 1 := by simpa only [d179269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21722 p hg
    simpa only [d179269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21890 (p : Pattern) (guard : d179270 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179270, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179270, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179269 p = 1 := by simpa only [d179270, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21889 p hg
    simpa only [d179270, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21891 (p : Pattern) (guard : d179271 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179271, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179271, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179270 p = 1 := by simpa only [d179271, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21890 p hg
    simpa only [d179271, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21892 (p : Pattern) (guard : d179272 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179271 p = 1 := by simpa only [d179272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21891 p hg
    simpa only [d179272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179149 p = 1 := by simpa only [d179272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21725 p hg
    simpa only [d179272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21893 (p : Pattern) (guard : d179273 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179272 p = 1 := by simpa only [d179273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21892 p hg
    simpa only [d179273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179150 p = 1 := by simpa only [d179273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21727 p hg
    simpa only [d179273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21894 (p : Pattern) (guard : d179274 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179273 p = 1 := by simpa only [d179274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21893 p hg
    simpa only [d179274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21895 (p : Pattern) (guard : d179275 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179274 p = 1 := by simpa only [d179275, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21894 p hg
    simpa only [d179275, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179275, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179275, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21896 (p : Pattern) (guard : d179276 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179276, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179276, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179275 p = 1 := by simpa only [d179276, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21895 p hg
    simpa only [d179276, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21897 (p : Pattern) (guard : d179277 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179276 p = 1 := by simpa only [d179277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21896 p hg
    simpa only [d179277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179154 p = 1 := by simpa only [d179277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21732 p hg
    simpa only [d179277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21898 (p : Pattern) (guard : d179278 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179277 p = 1 := by simpa only [d179278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21897 p hg
    simpa only [d179278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21899 (p : Pattern) (guard : d179279 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179278 p = 1 := by simpa only [d179279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21898 p hg
    simpa only [d179279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21900 (p : Pattern) (guard : d179280 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179279 p = 1 := by simpa only [d179280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21899 p hg
    simpa only [d179280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21901 (p : Pattern) (guard : d179281 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179280 p = 1 := by simpa only [d179281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21900 p hg
    simpa only [d179281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179158 p = 1 := by simpa only [d179281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21736 p hg
    simpa only [d179281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21902 (p : Pattern) (guard : d179282 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179281 p = 1 := by simpa only [d179282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21901 p hg
    simpa only [d179282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21903 (p : Pattern) (guard : d179283 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179282 p = 1 := by simpa only [d179283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21902 p hg
    simpa only [d179283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179160 p = 1 := by simpa only [d179283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21738 p hg
    simpa only [d179283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21904 (p : Pattern) (guard : d179284 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179283 p = 1 := by simpa only [d179284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21903 p hg
    simpa only [d179284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21905 (p : Pattern) (guard : d179285 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179284 p = 1 := by simpa only [d179285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21904 p hg
    simpa only [d179285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21906 (p : Pattern) (guard : d179286 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179286, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179286, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179285 p = 1 := by simpa only [d179286, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21905 p hg
    simpa only [d179286, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21907 (p : Pattern) (guard : d179287 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179286 p = 1 := by simpa only [d179287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21906 p hg
    simpa only [d179287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21908 (p : Pattern) (guard : d179288 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179287 p = 1 := by simpa only [d179288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21907 p hg
    simpa only [d179288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21909 (p : Pattern) (guard : d179289 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179288 p = 1 := by simpa only [d179289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21908 p hg
    simpa only [d179289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21910 (p : Pattern) (guard : d179290 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179289 p = 1 := by simpa only [d179290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21909 p hg
    simpa only [d179290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21911 (p : Pattern) (guard : d179291 p = 1) : d48387 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179290 p = 1 := by simpa only [d179291, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21910 p hg
    simpa only [d179291, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179291, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21747 p hg
    simpa only [d179291, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21912 (p : Pattern) (guard : d179292 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d179262 p = 1 := by simpa only [d179292, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21884 p hg
    simpa only [d179292, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179291 p = 1 := by simpa only [d179292, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21911 p hg
    simpa only [d179292, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21913 (p : Pattern) (guard : d179293 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179292 p = 1 := by simpa only [d179293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21912 p hg
    simpa only [d179293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21914 (p : Pattern) (guard : d179294 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179293 p = 1 := by simpa only [d179294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21913 p hg
    simpa only [d179294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21915 (p : Pattern) (guard : d179295 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179294 p = 1 := by simpa only [d179295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21914 p hg
    simpa only [d179295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21916 (p : Pattern) (guard : d179296 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179295 p = 1 := by simpa only [d179296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21915 p hg
    simpa only [d179296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21917 (p : Pattern) (guard : d179297 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179296 p = 1 := by simpa only [d179297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21916 p hg
    simpa only [d179297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21918 (p : Pattern) (guard : d179298 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179297 p = 1 := by simpa only [d179298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21917 p hg
    simpa only [d179298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21919 (p : Pattern) (guard : d179299 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d179176 p = 1 := by simpa only [d179299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21755 p hg
    simpa only [d179299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179298 p = 1 := by simpa only [d179299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21918 p hg
    simpa only [d179299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21920 (p : Pattern) (guard : d179300 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179214 p = 1 := by simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21790 p hg
    simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21921 (p : Pattern) (guard : d179301 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179301, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179301, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179300 p = 1 := by simpa only [d179301, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21920 p hg
    simpa only [d179301, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21922 (p : Pattern) (guard : d179302 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179302, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179302, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179301 p = 1 := by simpa only [d179302, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21921 p hg
    simpa only [d179302, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21923 (p : Pattern) (guard : d179303 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179302 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21922 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21924 (p : Pattern) (guard : d179304 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179303 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21923 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21925 (p : Pattern) (guard : d179305 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179304 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21924 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21926 (p : Pattern) (guard : d179306 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179305 p = 1 := by simpa only [d179306, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21925 p hg
    simpa only [d179306, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179306, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179306, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21927 (p : Pattern) (guard : d179307 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179307, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179307, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179306 p = 1 := by simpa only [d179307, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21926 p hg
    simpa only [d179307, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21928 (p : Pattern) (guard : d179308 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179307 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21927 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21929 (p : Pattern) (guard : d179309 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179308 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21928 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21930 (p : Pattern) (guard : d179310 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179309 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21929 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21931 (p : Pattern) (guard : d179311 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179310 p = 1 := by simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21930 p hg
    simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21932 (p : Pattern) (guard : d179312 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179311 p = 1 := by simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21931 p hg
    simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21933 (p : Pattern) (guard : d179313 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179312 p = 1 := by simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21932 p hg
    simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21934 (p : Pattern) (guard : d179314 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179313 p = 1 := by simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21933 p hg
    simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21935 (p : Pattern) (guard : d179315 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179314 p = 1 := by simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21934 p hg
    simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21936 (p : Pattern) (guard : d179316 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179315 p = 1 := by simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21935 p hg
    simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21937 (p : Pattern) (guard : d179317 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179317, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179317, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179316 p = 1 := by simpa only [d179317, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21936 p hg
    simpa only [d179317, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21938 (p : Pattern) (guard : d179318 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179317 p = 1 := by simpa only [d179318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21937 p hg
    simpa only [d179318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21939 (p : Pattern) (guard : d179319 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179318 p = 1 := by simpa only [d179319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21938 p hg
    simpa only [d179319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21940 (p : Pattern) (guard : d179302 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179302, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179302, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179301 p = 1 := by simpa only [d179302, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21921 p hg
    simpa only [d179302, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21941 (p : Pattern) (guard : d179303 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179302 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21940 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21942 (p : Pattern) (guard : d179304 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179303 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21941 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21943 (p : Pattern) (guard : d179305 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179304 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21942 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21944 (p : Pattern) (guard : d179306 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179305 p = 1 := by simpa only [d179306, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21943 p hg
    simpa only [d179306, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179306, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179306, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21945 (p : Pattern) (guard : d179307 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179307, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179307, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179306 p = 1 := by simpa only [d179307, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21944 p hg
    simpa only [d179307, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21946 (p : Pattern) (guard : d179308 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179307 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21945 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21947 (p : Pattern) (guard : d179309 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179308 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21946 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21948 (p : Pattern) (guard : d179310 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179309 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21947 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21949 (p : Pattern) (guard : d179311 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179310 p = 1 := by simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21948 p hg
    simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21950 (p : Pattern) (guard : d179312 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179311 p = 1 := by simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21949 p hg
    simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21951 (p : Pattern) (guard : d179313 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179312 p = 1 := by simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21950 p hg
    simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21952 (p : Pattern) (guard : d179314 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179313 p = 1 := by simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21951 p hg
    simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21953 (p : Pattern) (guard : d179315 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179314 p = 1 := by simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21952 p hg
    simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21954 (p : Pattern) (guard : d179316 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179315 p = 1 := by simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21953 p hg
    simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21955 (p : Pattern) (guard : d179320 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179310 p = 1 := by simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21930 p hg
    simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21956 (p : Pattern) (guard : d179321 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179320 p = 1 := by simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21955 p hg
    simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21957 (p : Pattern) (guard : d179322 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179321 p = 1 := by simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21956 p hg
    simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21958 (p : Pattern) (guard : d179323 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179322 p = 1 := by simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21957 p hg
    simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21959 (p : Pattern) (guard : d179324 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179323 p = 1 := by simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21958 p hg
    simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21960 (p : Pattern) (guard : d179325 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179324 p = 1 := by simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21959 p hg
    simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21961 (p : Pattern) (guard : d179326 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179316 p = 1 := by simpa only [d179326, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21954 p hg
    simpa only [d179326, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179325 p = 1 := by simpa only [d179326, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21960 p hg
    simpa only [d179326, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21962 (p : Pattern) (guard : d179327 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179317 p = 1 := by simpa only [d179327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21937 p hg
    simpa only [d179327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179326 p = 1 := by simpa only [d179327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21961 p hg
    simpa only [d179327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21963 (p : Pattern) (guard : d179328 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179327 p = 1 := by simpa only [d179328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21962 p hg
    simpa only [d179328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21964 (p : Pattern) (guard : d179329 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179319 p = 1 := by simpa only [d179329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21939 p hg
    simpa only [d179329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179328 p = 1 := by simpa only [d179329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21963 p hg
    simpa only [d179329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21965 (p : Pattern) (guard : d179330 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179309 p = 1 := by simpa only [d179330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21929 p hg
    simpa only [d179330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21966 (p : Pattern) (guard : d179331 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179330 p = 1 := by simpa only [d179331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21965 p hg
    simpa only [d179331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21967 (p : Pattern) (guard : d179332 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179331 p = 1 := by simpa only [d179332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21966 p hg
    simpa only [d179332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21968 (p : Pattern) (guard : d179333 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179332 p = 1 := by simpa only [d179333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21967 p hg
    simpa only [d179333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21969 (p : Pattern) (guard : d179334 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179333 p = 1 := by simpa only [d179334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21968 p hg
    simpa only [d179334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21970 (p : Pattern) (guard : d179335 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179334 p = 1 := by simpa only [d179335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21969 p hg
    simpa only [d179335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21971 (p : Pattern) (guard : d179336 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179308 p = 1 := by simpa only [d179336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21928 p hg
    simpa only [d179336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21972 (p : Pattern) (guard : d179337 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179336 p = 1 := by simpa only [d179337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21971 p hg
    simpa only [d179337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21973 (p : Pattern) (guard : d179338 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179337 p = 1 := by simpa only [d179338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21972 p hg
    simpa only [d179338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21974 (p : Pattern) (guard : d179339 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179338 p = 1 := by simpa only [d179339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21973 p hg
    simpa only [d179339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21975 (p : Pattern) (guard : d179340 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179339 p = 1 := by simpa only [d179340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21974 p hg
    simpa only [d179340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21976 (p : Pattern) (guard : d179341 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179340 p = 1 := by simpa only [d179341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21975 p hg
    simpa only [d179341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21977 (p : Pattern) (guard : d179354 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare21978 (p : Pattern) (guard : d179355 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179354 p = 1 := by simpa only [d179355, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21977 p hg
    simpa only [d179355, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179355, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179355, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21979 (p : Pattern) (guard : d179356 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179355 p = 1 := by simpa only [d179356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21978 p hg
    simpa only [d179356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21980 (p : Pattern) (guard : d179357 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179356 p = 1 := by simpa only [d179357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21979 p hg
    simpa only [d179357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21981 (p : Pattern) (guard : d179358 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179357 p = 1 := by simpa only [d179358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21980 p hg
    simpa only [d179358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179214 p = 1 := by simpa only [d179358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21790 p hg
    simpa only [d179358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21982 (p : Pattern) (guard : d179359 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179359, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179359, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179358 p = 1 := by simpa only [d179359, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21981 p hg
    simpa only [d179359, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21983 (p : Pattern) (guard : d179360 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179360, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179360, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179359 p = 1 := by simpa only [d179360, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21982 p hg
    simpa only [d179360, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21984 (p : Pattern) (guard : d179361 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179360 p = 1 := by simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21983 p hg
    simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179302 p = 1 := by simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21922 p hg
    simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21985 (p : Pattern) (guard : d179362 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179361 p = 1 := by simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21984 p hg
    simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179303 p = 1 := by simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21923 p hg
    simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21986 (p : Pattern) (guard : d179363 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179362 p = 1 := by simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21985 p hg
    simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21987 (p : Pattern) (guard : d179364 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179363 p = 1 := by simpa only [d179364, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21986 p hg
    simpa only [d179364, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179364, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179364, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21988 (p : Pattern) (guard : d179365 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179365, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179365, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179364 p = 1 := by simpa only [d179365, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21987 p hg
    simpa only [d179365, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21989 (p : Pattern) (guard : d179366 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179365 p = 1 := by simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21988 p hg
    simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179307 p = 1 := by simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21927 p hg
    simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21990 (p : Pattern) (guard : d179367 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179366 p = 1 := by simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21989 p hg
    simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21991 (p : Pattern) (guard : d179368 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179367 p = 1 := by simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21990 p hg
    simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21992 (p : Pattern) (guard : d179369 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179368 p = 1 := by simpa only [d179369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21991 p hg
    simpa only [d179369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21993 (p : Pattern) (guard : d179370 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179369 p = 1 := by simpa only [d179370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21992 p hg
    simpa only [d179370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179311 p = 1 := by simpa only [d179370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21931 p hg
    simpa only [d179370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21994 (p : Pattern) (guard : d179371 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179370 p = 1 := by simpa only [d179371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21993 p hg
    simpa only [d179371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21995 (p : Pattern) (guard : d179372 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179312 p = 1 := by simpa only [d179372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21932 p hg
    simpa only [d179372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21996 (p : Pattern) (guard : d179373 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179371 p = 1 := by simpa only [d179373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21994 p hg
    simpa only [d179373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179372 p = 1 := by simpa only [d179373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21995 p hg
    simpa only [d179373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21997 (p : Pattern) (guard : d179374 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179341 p = 1 := by simpa only [d179374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21976 p hg
    simpa only [d179374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179373 p = 1 := by simpa only [d179374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21996 p hg
    simpa only [d179374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21998 (p : Pattern) (guard : d179375 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179335 p = 1 := by simpa only [d179375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21970 p hg
    simpa only [d179375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179374 p = 1 := by simpa only [d179375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21997 p hg
    simpa only [d179375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21999 (p : Pattern) (guard : d179376 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179376, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179376, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179375 p = 1 := by simpa only [d179376, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21998 p hg
    simpa only [d179376, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
