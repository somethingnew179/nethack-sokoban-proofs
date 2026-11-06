/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13020 (p : Pattern) (guard : d4985 p = 1) : d1641 p ≤ (0 : Int) + d5174 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1641, d5174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13018 p hg
    simpa only [d1641, d5174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1641, d5174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13019 p hg
    simpa only [d1641, d5174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13021 (p : Pattern) (guard : d4985 p = 1) : d215 p ≤ (0 : Int) + d215 p := by
  omega
theorem compare13022 (p : Pattern) (guard : d4985 p = 1) : d1642 p ≤ (0 : Int) + d5175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1642, d5175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12896 p hg
    simpa only [d1642, d5175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1642, d5175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13021 p hg
    simpa only [d1642, d5175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13023 (p : Pattern) (guard : d4985 p = 1) : d217 p ≤ (0 : Int) + d217 p := by
  omega
theorem compare13024 (p : Pattern) (guard : d4985 p = 1) : d1643 p ≤ (0 : Int) + d5176 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1643, d5176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13022 p hg
    simpa only [d1643, d5176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1643, d5176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13023 p hg
    simpa only [d1643, d5176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13025 (p : Pattern) (guard : d4985 p = 1) : d1644 p ≤ (0 : Int) + d5177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1644, d5177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13020 p hg
    simpa only [d1644, d5177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1644, d5177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13024 p hg
    simpa only [d1644, d5177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13026 (p : Pattern) (guard : d4985 p = 1) : d1645 p ≤ (0 : Int) + d5178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1645, d5178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12883 p hg
    simpa only [d1645, d5178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1645, d5178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13025 p hg
    simpa only [d1645, d5178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13027 (p : Pattern) (guard : d4985 p = 1) : d215 p ≤ (0 : Int) + d5179 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d215, d5179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12911 p hg
    simpa only [d215, d5179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d215, d5179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d215, d5179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13028 (p : Pattern) (guard : d4985 p = 1) : d1642 p ≤ (0 : Int) + d5180 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1642, d5180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12923 p hg
    simpa only [d1642, d5180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1642, d5180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13027 p hg
    simpa only [d1642, d5180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13029 (p : Pattern) (guard : d4985 p = 1) : d217 p ≤ (0 : Int) + d5181 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d217, d5181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13027 p hg
    simpa only [d217, d5181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d217, d5181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d217, d5181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13030 (p : Pattern) (guard : d4985 p = 1) : d1643 p ≤ (0 : Int) + d5182 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1643, d5182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13028 p hg
    simpa only [d1643, d5182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1643, d5182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13029 p hg
    simpa only [d1643, d5182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13031 (p : Pattern) (guard : d4985 p = 1) : d1646 p ≤ (0 : Int) + d5183 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1646, d5183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13030 p hg
    simpa only [d1646, d5183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1646, d5183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12931 p hg
    simpa only [d1646, d5183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13032 (p : Pattern) (guard : d4985 p = 1) : d1647 p ≤ (0 : Int) + d5184 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1647, d5184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12922 p hg
    simpa only [d1647, d5184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1647, d5184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13031 p hg
    simpa only [d1647, d5184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13033 (p : Pattern) (guard : d4985 p = 1) : d1648 p ≤ (0 : Int) + d5185 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1648, d5185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13026 p hg
    simpa only [d1648, d5185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1648, d5185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13032 p hg
    simpa only [d1648, d5185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13034 (p : Pattern) (guard : d4985 p = 1) : d1649 p ≤ (0 : Int) + d5186 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1649, d5186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13032 p hg
    simpa only [d1649, d5186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1649, d5186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12938 p hg
    simpa only [d1649, d5186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13035 (p : Pattern) (guard : d4985 p = 1) : d1650 p ≤ (0 : Int) + d5187 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1650, d5187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13033 p hg
    simpa only [d1650, d5187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1650, d5187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13034 p hg
    simpa only [d1650, d5187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13036 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d1942 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13037 (p : Pattern) (guard : d4985 p = 1) : d1573 p ≤ (0 : Int) + d5084 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1573, d5084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d1573, d5084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1573, d5084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13036 p hg
    simpa only [d4985, d1573, d5084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13038 (p : Pattern) (guard : d4985 p = 1) : d1601 p ≤ (0 : Int) + d5084 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13037 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12904 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13039 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13040 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d124, d5188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d124, d5188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d124, d5188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13039 p hg
    simpa only [d4985, d124, d5188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13041 (p : Pattern) (guard : d4985 p = 1) : d126 p ≤ (0 : Int) + d5189 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d126, d5189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13040 p hg
    simpa only [d126, d5189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d126, d5189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12911 p hg
    simpa only [d126, d5189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13042 (p : Pattern) (guard : d4985 p = 1) : d1602 p ≤ (0 : Int) + d5190 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1602, d5190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13038 p hg
    simpa only [d1602, d5190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1602, d5190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13041 p hg
    simpa only [d1602, d5190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13043 (p : Pattern) (guard : d4985 p = 1) : d126 p ≤ (0 : Int) + d5191 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d126, d5191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12906 p hg
    simpa only [d126, d5191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d126, d5191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12911 p hg
    simpa only [d126, d5191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13044 (p : Pattern) (guard : d4985 p = 1) : d129 p ≤ (0 : Int) + d5192 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d129, d5192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13043 p hg
    simpa only [d129, d5192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d129, d5192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12871 p hg
    simpa only [d129, d5192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13045 (p : Pattern) (guard : d4985 p = 1) : d1603 p ≤ (0 : Int) + d5193 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1603, d5193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13042 p hg
    simpa only [d1603, d5193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1603, d5193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13044 p hg
    simpa only [d1603, d5193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13046 (p : Pattern) (guard : d4985 p = 1) : d139 p ≤ (0 : Int) + d5194 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d139, d5194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12886 p hg
    simpa only [d4985, d139, d5194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d139, d5194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12876 p hg
    simpa only [d4985, d139, d5194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13047 (p : Pattern) (guard : d4985 p = 1) : d139 p ≤ (0 : Int) + d5195 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12916 p hg
    simpa only [d5195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13046 p hg
    simpa only [d5195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13048 (p : Pattern) (guard : d4985 p = 1) : d1651 p ≤ (0 : Int) + d5196 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1651, d5196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13047 p hg
    simpa only [d1651, d5196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1651, d5196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13021 p hg
    simpa only [d1651, d5196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13049 (p : Pattern) (guard : d4985 p = 1) : d231 p ≤ (0 : Int) + d231 p := by
  omega
theorem compare13050 (p : Pattern) (guard : d4985 p = 1) : d1652 p ≤ (0 : Int) + d5197 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1652, d5197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13048 p hg
    simpa only [d1652, d5197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1652, d5197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13049 p hg
    simpa only [d1652, d5197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13051 (p : Pattern) (guard : d4985 p = 1) : d1653 p ≤ (0 : Int) + d5198 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1653, d5198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13045 p hg
    simpa only [d1653, d5198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1653, d5198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13050 p hg
    simpa only [d1653, d5198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13052 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13053 (p : Pattern) (guard : d4985 p = 1) : d139 p ≤ (0 : Int) + d5199 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d139, d5199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12886 p hg
    simpa only [d4985, d139, d5199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d139, d5199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13052 p hg
    simpa only [d4985, d139, d5199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13054 (p : Pattern) (guard : d4985 p = 1) : d1584 p ≤ (0 : Int) + d5200 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1584, d5200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13040 p hg
    simpa only [d1584, d5200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1584, d5200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13053 p hg
    simpa only [d1584, d5200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13055 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13056 (p : Pattern) (guard : d4985 p = 1) : d125 p ≤ (0 : Int) + d5201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d125, d5201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d4985, d125, d5201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d125, d5201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13055 p hg
    simpa only [d4985, d125, d5201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13057 (p : Pattern) (guard : d4985 p = 1) : d215 p ≤ (0 : Int) + d5202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d215, d5202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13056 p hg
    simpa only [d215, d5202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d215, d5202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d215, d5202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13058 (p : Pattern) (guard : d4985 p = 1) : d1642 p ≤ (0 : Int) + d5203 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1642, d5203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13054 p hg
    simpa only [d1642, d5203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1642, d5203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13057 p hg
    simpa only [d1642, d5203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13059 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2136 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13060 (p : Pattern) (guard : d4985 p = 1) : d125 p ≤ (0 : Int) + d5204 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d125, d5204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d4985, d125, d5204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d125, d5204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13059 p hg
    simpa only [d4985, d125, d5204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13061 (p : Pattern) (guard : d4985 p = 1) : d215 p ≤ (0 : Int) + d5205 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d215, d5205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13060 p hg
    simpa only [d215, d5205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d215, d5205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d215, d5205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13062 (p : Pattern) (guard : d4985 p = 1) : d217 p ≤ (0 : Int) + d5206 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d217, d5206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13061 p hg
    simpa only [d217, d5206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d217, d5206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d217, d5206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13063 (p : Pattern) (guard : d4985 p = 1) : d1643 p ≤ (0 : Int) + d5207 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1643, d5207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13058 p hg
    simpa only [d1643, d5207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1643, d5207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13062 p hg
    simpa only [d1643, d5207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13064 (p : Pattern) (guard : d4985 p = 1) : d125 p ≤ (0 : Int) + d5208 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d125, d5208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d4985, d125, d5208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d125, d5208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12876 p hg
    simpa only [d4985, d125, d5208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13065 (p : Pattern) (guard : d4985 p = 1) : d125 p ≤ (0 : Int) + d125 p := by
  omega
theorem compare13066 (p : Pattern) (guard : d4985 p = 1) : d125 p ≤ (0 : Int) + d5209 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13064 p hg
    simpa only [d5209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13065 p hg
    simpa only [d5209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13067 (p : Pattern) (guard : d4985 p = 1) : d230 p ≤ (0 : Int) + d230 p := by
  omega
theorem compare13068 (p : Pattern) (guard : d4985 p = 1) : d1654 p ≤ (0 : Int) + d5210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1654, d5210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13066 p hg
    simpa only [d1654, d5210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1654, d5210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13067 p hg
    simpa only [d1654, d5210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13069 (p : Pattern) (guard : d4985 p = 1) : d237 p ≤ (0 : Int) + d237 p := by
  omega
theorem compare13070 (p : Pattern) (guard : d4985 p = 1) : d1655 p ≤ (0 : Int) + d5211 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1655, d5211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13068 p hg
    simpa only [d1655, d5211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1655, d5211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13069 p hg
    simpa only [d1655, d5211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13071 (p : Pattern) (guard : d4985 p = 1) : d1656 p ≤ (0 : Int) + d5212 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1656, d5212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13063 p hg
    simpa only [d1656, d5212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1656, d5212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13070 p hg
    simpa only [d1656, d5212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13072 (p : Pattern) (guard : d4985 p = 1) : d1657 p ≤ (0 : Int) + d5213 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1657, d5213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13051 p hg
    simpa only [d1657, d5213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1657, d5213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13071 p hg
    simpa only [d1657, d5213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13073 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5214 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12906 p hg
    simpa only [d5214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12909 p hg
    simpa only [d5214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13074 (p : Pattern) (guard : d4985 p = 1) : d1658 p ≤ (0 : Int) + d5215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1658, d5215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12916 p hg
    simpa only [d1658, d5215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1658, d5215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12758 p hg
    simpa only [d1658, d5215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13075 (p : Pattern) (guard : d4985 p = 1) : d1659 p ≤ (0 : Int) + d5216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1659, d5216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13073 p hg
    simpa only [d1659, d5216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1659, d5216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13074 p hg
    simpa only [d1659, d5216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13076 (p : Pattern) (guard : d4985 p = 1) : d1660 p ≤ (0 : Int) + d5217 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1660, d5217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13075 p hg
    simpa only [d1660, d5217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1660, d5217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12927 p hg
    simpa only [d1660, d5217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13077 (p : Pattern) (guard : d4985 p = 1) : d1661 p ≤ (0 : Int) + d5218 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1661, d5218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13076 p hg
    simpa only [d1661, d5218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1661, d5218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12931 p hg
    simpa only [d1661, d5218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13078 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13079 (p : Pattern) (guard : d4985 p = 1) : d139 p ≤ (0 : Int) + d5219 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d139, d5219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12886 p hg
    simpa only [d4985, d139, d5219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d139, d5219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13078 p hg
    simpa only [d4985, d139, d5219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13080 (p : Pattern) (guard : d4985 p = 1) : d139 p ≤ (0 : Int) + d5220 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13079 p hg
    simpa only [d5220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12916 p hg
    simpa only [d5220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13081 (p : Pattern) (guard : d4985 p = 1) : d1651 p ≤ (0 : Int) + d5221 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1651, d5221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13080 p hg
    simpa only [d1651, d5221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1651, d5221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13027 p hg
    simpa only [d1651, d5221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13082 (p : Pattern) (guard : d4985 p = 1) : d1652 p ≤ (0 : Int) + d5222 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1652, d5222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13081 p hg
    simpa only [d1652, d5222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1652, d5222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12930 p hg
    simpa only [d1652, d5222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13083 (p : Pattern) (guard : d4985 p = 1) : d237 p ≤ (0 : Int) + d5223 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d237, d5223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12783 p hg
    simpa only [d237, d5223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d237, d5223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d237, d5223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13084 (p : Pattern) (guard : d4985 p = 1) : d1662 p ≤ (0 : Int) + d5224 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1662, d5224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13083 p hg
    simpa only [d1662, d5224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1662, d5224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1662, d5224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13085 (p : Pattern) (guard : d4985 p = 1) : d1663 p ≤ (0 : Int) + d5225 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1663, d5225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13082 p hg
    simpa only [d1663, d5225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1663, d5225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13084 p hg
    simpa only [d1663, d5225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13086 (p : Pattern) (guard : d4985 p = 1) : d1664 p ≤ (0 : Int) + d5226 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1664, d5226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13077 p hg
    simpa only [d1664, d5226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1664, d5226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13085 p hg
    simpa only [d1664, d5226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13087 (p : Pattern) (guard : d4985 p = 1) : d1665 p ≤ (0 : Int) + d5227 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1665, d5227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13072 p hg
    simpa only [d1665, d5227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1665, d5227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13086 p hg
    simpa only [d1665, d5227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13088 (p : Pattern) (guard : d4985 p = 1) : d1666 p ≤ (0 : Int) + d5228 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1666, d5228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12916 p hg
    simpa only [d1666, d5228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1666, d5228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12782 p hg
    simpa only [d1666, d5228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13089 (p : Pattern) (guard : d4985 p = 1) : d1667 p ≤ (0 : Int) + d5229 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1667, d5229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13073 p hg
    simpa only [d1667, d5229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1667, d5229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13088 p hg
    simpa only [d1667, d5229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13090 (p : Pattern) (guard : d4985 p = 1) : d1668 p ≤ (0 : Int) + d5230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1668, d5230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12911 p hg
    simpa only [d1668, d5230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1668, d5230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12782 p hg
    simpa only [d1668, d5230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13091 (p : Pattern) (guard : d4985 p = 1) : d1669 p ≤ (0 : Int) + d5231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1669, d5231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13090 p hg
    simpa only [d1669, d5231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1669, d5231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1669, d5231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13092 (p : Pattern) (guard : d4985 p = 1) : d1670 p ≤ (0 : Int) + d5232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1670, d5232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13089 p hg
    simpa only [d1670, d5232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1670, d5232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13091 p hg
    simpa only [d1670, d5232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13093 (p : Pattern) (guard : d4985 p = 1) : d1671 p ≤ (0 : Int) + d5233 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1671, d5233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12918 p hg
    simpa only [d1671, d5233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1671, d5233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12758 p hg
    simpa only [d1671, d5233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13094 (p : Pattern) (guard : d4985 p = 1) : d1672 p ≤ (0 : Int) + d5234 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1672, d5234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13093 p hg
    simpa only [d1672, d5234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1672, d5234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1672, d5234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13095 (p : Pattern) (guard : d4985 p = 1) : d1673 p ≤ (0 : Int) + d5235 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1673, d5235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13094 p hg
    simpa only [d1673, d5235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1673, d5235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1673, d5235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13096 (p : Pattern) (guard : d4985 p = 1) : d1674 p ≤ (0 : Int) + d5236 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1674, d5236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13092 p hg
    simpa only [d1674, d5236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1674, d5236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13095 p hg
    simpa only [d1674, d5236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13097 (p : Pattern) (guard : d4985 p = 1) : d1675 p ≤ (0 : Int) + d5237 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1675, d5237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13096 p hg
    simpa only [d1675, d5237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1675, d5237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13085 p hg
    simpa only [d1675, d5237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13098 (p : Pattern) (guard : d4985 p = 1) : d1676 p ≤ (0 : Int) + d5238 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1676, d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13097 p hg
    simpa only [d1676, d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1676, d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1676, d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13099 (p : Pattern) (guard : d4985 p = 1) : d1677 p ≤ (0 : Int) + d5239 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1677, d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13087 p hg
    simpa only [d1677, d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1677, d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13098 p hg
    simpa only [d1677, d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13100 (p : Pattern) (guard : d4985 p = 1) : d1678 p ≤ (0 : Int) + d5240 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1678, d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13035 p hg
    simpa only [d1678, d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1678, d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13099 p hg
    simpa only [d1678, d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13101 (p : Pattern) (guard : d4985 p = 1) : d1679 p ≤ (0 : Int) + d5241 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1679, d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12834 p hg
    simpa only [d1679, d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1679, d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13100 p hg
    simpa only [d1679, d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13102 (p : Pattern) (guard : d4985 p = 1) : d1680 p ≤ (0 : Int) + d5242 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1680, d5242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13016 p hg
    simpa only [d1680, d5242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1680, d5242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13101 p hg
    simpa only [d1680, d5242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13103 (p : Pattern) (guard : d4985 p = 1) : d1681 p ≤ (0 : Int) + d5243 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1681, d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12955 p hg
    simpa only [d1681, d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1681, d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13102 p hg
    simpa only [d1681, d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13104 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (0 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d46, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d4206, d46, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13105 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (0 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d46, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3074 p hg
    simpa only [d4206, d46, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13106 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13104 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13105 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13107 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (0 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d46, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2944 p hg
    simpa only [d4206, d46, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13108 (p : Pattern) (guard : d4206 p = 1) : d47 p ≤ (0 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d47, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13107 p hg
    simpa only [d47, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d47, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d47, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13109 (p : Pattern) (guard : d4206 p = 1) : d1511 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1511, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13106 p hg
    simpa only [d1511, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1511, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13108 p hg
    simpa only [d1511, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13110 (p : Pattern) (guard : d4206 p = 1) : d1512 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1512, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13109 p hg
    simpa only [d1512, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1512, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5072 p hg
    simpa only [d1512, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13111 (p : Pattern) (guard : d4206 p = 1) : d1513 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1513, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11873 p hg
    simpa only [d1513, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1513, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13110 p hg
    simpa only [d1513, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13112 (p : Pattern) (guard : d4206 p = 1) : d1518 p ≤ (0 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1518, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13105 p hg
    simpa only [d1518, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1518, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5088 p hg
    simpa only [d1518, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13113 (p : Pattern) (guard : d4206 p = 1) : d1519 p ≤ (0 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1519, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13112 p hg
    simpa only [d1519, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1519, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5090 p hg
    simpa only [d1519, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13114 (p : Pattern) (guard : d4206 p = 1) : d1520 p ≤ (0 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1520, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13113 p hg
    simpa only [d1520, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1520, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5092 p hg
    simpa only [d1520, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13115 (p : Pattern) (guard : d4206 p = 1) : d1521 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1521, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11887 p hg
    simpa only [d1521, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1521, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13114 p hg
    simpa only [d1521, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13116 (p : Pattern) (guard : d4206 p = 1) : d1522 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1522, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13111 p hg
    simpa only [d1522, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1522, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13115 p hg
    simpa only [d1522, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13117 (p : Pattern) (guard : d4206 p = 1) : d1523 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1523, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12027 p hg
    simpa only [d1523, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1523, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1523, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13118 (p : Pattern) (guard : d4206 p = 1) : d1524 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1524, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11892 p hg
    simpa only [d1524, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1524, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13117 p hg
    simpa only [d1524, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13119 (p : Pattern) (guard : d4206 p = 1) : d1525 p ≤ (0 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1525, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12034 p hg
    simpa only [d1525, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1525, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1525, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13120 (p : Pattern) (guard : d4206 p = 1) : d1526 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1526, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11897 p hg
    simpa only [d1526, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1526, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13119 p hg
    simpa only [d1526, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13121 (p : Pattern) (guard : d4206 p = 1) : d1527 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1527, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13118 p hg
    simpa only [d1527, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1527, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13120 p hg
    simpa only [d1527, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13122 (p : Pattern) (guard : d4206 p = 1) : d1528 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1528, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13116 p hg
    simpa only [d1528, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1528, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13121 p hg
    simpa only [d1528, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13123 (p : Pattern) (guard : d4206 p = 1) : d1532 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1532, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11904 p hg
    simpa only [d1532, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1532, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13117 p hg
    simpa only [d1532, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13124 (p : Pattern) (guard : d4206 p = 1) : d1533 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1533, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13123 p hg
    simpa only [d1533, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1533, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13120 p hg
    simpa only [d1533, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13125 (p : Pattern) (guard : d4206 p = 1) : d1539 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1539, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11911 p hg
    simpa only [d1539, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1539, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11914 p hg
    simpa only [d1539, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13126 (p : Pattern) (guard : d4206 p = 1) : d1540 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11914 p hg
    simpa only [d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13127 (p : Pattern) (guard : d4206 p = 1) : d1541 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1541, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13125 p hg
    simpa only [d1541, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1541, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13126 p hg
    simpa only [d1541, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13128 (p : Pattern) (guard : d4206 p = 1) : d1542 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1542, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13124 p hg
    simpa only [d1542, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1542, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13127 p hg
    simpa only [d1542, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13129 (p : Pattern) (guard : d4206 p = 1) : d1543 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1543, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13122 p hg
    simpa only [d1543, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1543, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13128 p hg
    simpa only [d1543, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13130 (p : Pattern) (guard : d4206 p = 1) : d1547 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1547, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11921 p hg
    simpa only [d1547, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1547, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13110 p hg
    simpa only [d1547, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13131 (p : Pattern) (guard : d4206 p = 1) : d1520 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11897 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13114 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13132 (p : Pattern) (guard : d4206 p = 1) : d1548 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1548, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13130 p hg
    simpa only [d1548, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1548, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13131 p hg
    simpa only [d1548, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13133 (p : Pattern) (guard : d4206 p = 1) : d1549 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1549, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13132 p hg
    simpa only [d1549, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1549, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13121 p hg
    simpa only [d1549, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13134 (p : Pattern) (guard : d4206 p = 1) : d1550 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1550, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13121 p hg
    simpa only [d1550, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1550, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1550, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13135 (p : Pattern) (guard : d4206 p = 1) : d1551 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1551, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13133 p hg
    simpa only [d1551, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1551, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13134 p hg
    simpa only [d1551, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13136 (p : Pattern) (guard : d4206 p = 1) : d1552 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1552, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13129 p hg
    simpa only [d1552, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1552, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13135 p hg
    simpa only [d1552, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13137 (p : Pattern) (guard : d4206 p = 1) : d1557 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1557, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11938 p hg
    simpa only [d1557, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1557, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13110 p hg
    simpa only [d1557, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13138 (p : Pattern) (guard : d4206 p = 1) : d1561 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1561, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11943 p hg
    simpa only [d1561, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1561, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13114 p hg
    simpa only [d1561, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13139 (p : Pattern) (guard : d4206 p = 1) : d1562 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1562, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13137 p hg
    simpa only [d1562, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1562, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13138 p hg
    simpa only [d1562, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13140 (p : Pattern) (guard : d4206 p = 1) : d1563 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1563, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13139 p hg
    simpa only [d1563, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1563, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13121 p hg
    simpa only [d1563, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13141 (p : Pattern) (guard : d4206 p = 1) : d1564 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1564, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13121 p hg
    simpa only [d1564, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1564, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13127 p hg
    simpa only [d1564, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13142 (p : Pattern) (guard : d4206 p = 1) : d1565 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1565, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13140 p hg
    simpa only [d1565, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1565, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13141 p hg
    simpa only [d1565, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13143 (p : Pattern) (guard : d4206 p = 1) : d1566 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1566, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11904 p hg
    simpa only [d1566, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1566, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13110 p hg
    simpa only [d1566, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13144 (p : Pattern) (guard : d4206 p = 1) : d1567 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1567, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13143 p hg
    simpa only [d1567, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1567, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13131 p hg
    simpa only [d1567, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13145 (p : Pattern) (guard : d4206 p = 1) : d1568 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1568, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13144 p hg
    simpa only [d1568, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1568, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13121 p hg
    simpa only [d1568, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13146 (p : Pattern) (guard : d4206 p = 1) : d1569 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1569, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13145 p hg
    simpa only [d1569, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1569, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13134 p hg
    simpa only [d1569, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13147 (p : Pattern) (guard : d4206 p = 1) : d1570 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1570, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13142 p hg
    simpa only [d1570, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1570, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13146 p hg
    simpa only [d1570, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13148 (p : Pattern) (guard : d4206 p = 1) : d1571 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13136 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13147 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13149 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (0 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d124, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d124, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d124, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d4206, d124, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13150 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (0 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d124, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d124, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d124, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3161 p hg
    simpa only [d4206, d124, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13151 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13149 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13150 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13152 (p : Pattern) (guard : d4206 p = 1) : d1577 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1577, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13151 p hg
    simpa only [d1577, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1577, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5176 p hg
    simpa only [d1577, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13153 (p : Pattern) (guard : d4206 p = 1) : d1578 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1578, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13152 p hg
    simpa only [d1578, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1578, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5178 p hg
    simpa only [d1578, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13154 (p : Pattern) (guard : d4206 p = 1) : d1579 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1579, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11970 p hg
    simpa only [d1579, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1579, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13153 p hg
    simpa only [d1579, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13155 (p : Pattern) (guard : d4206 p = 1) : d1584 p ≤ (0 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1584, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13150 p hg
    simpa only [d1584, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1584, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5190 p hg
    simpa only [d1584, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13156 (p : Pattern) (guard : d4206 p = 1) : d1585 p ≤ (0 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1585, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13155 p hg
    simpa only [d1585, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1585, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5192 p hg
    simpa only [d1585, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13157 (p : Pattern) (guard : d4206 p = 1) : d1586 p ≤ (0 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1586, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13156 p hg
    simpa only [d1586, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1586, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5194 p hg
    simpa only [d1586, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13158 (p : Pattern) (guard : d4206 p = 1) : d1587 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1587, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11981 p hg
    simpa only [d1587, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1587, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13157 p hg
    simpa only [d1587, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13159 (p : Pattern) (guard : d4206 p = 1) : d1588 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1588, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13154 p hg
    simpa only [d1588, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1588, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13158 p hg
    simpa only [d1588, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
