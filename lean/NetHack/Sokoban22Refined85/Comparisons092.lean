/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons091
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12880 (p : Pattern) (guard : d4985 p = 1) : d1577 p ≤ (0 : Int) + d5069 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1577, d5069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12878 p hg
    simpa only [d1577, d5069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1577, d5069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12879 p hg
    simpa only [d1577, d5069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12881 (p : Pattern) (guard : d4985 p = 1) : d129 p ≤ (0 : Int) + d129 p := by
  omega
theorem compare12882 (p : Pattern) (guard : d4985 p = 1) : d1578 p ≤ (0 : Int) + d5070 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1578, d5070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d1578, d5070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1578, d5070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12881 p hg
    simpa only [d1578, d5070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12883 (p : Pattern) (guard : d4985 p = 1) : d1579 p ≤ (0 : Int) + d5071 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1579, d5071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d1579, d5071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1579, d5071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12882 p hg
    simpa only [d1579, d5071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12884 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (0 : Int) + d1875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12885 (p : Pattern) (guard : d4985 p = 1) : d1580 p ≤ (0 : Int) + d5059 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1580, d5059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d1580, d5059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1580, d5059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d4985, d1580, d5059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12886 (p : Pattern) (guard : d4473 p = 1) : d116 p ≤ (0 : Int) + d116 p := by
  omega
theorem compare12887 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1921 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12888 (p : Pattern) (guard : d4985 p = 1) : d139 p ≤ (0 : Int) + d5072 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d139, d5072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12886 p hg
    simpa only [d4985, d139, d5072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d139, d5072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12887 p hg
    simpa only [d4985, d139, d5072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12889 (p : Pattern) (guard : d4985 p = 1) : d1581 p ≤ (0 : Int) + d5073 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1581, d5073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12885 p hg
    simpa only [d1581, d5073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1581, d5073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12888 p hg
    simpa only [d1581, d5073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12890 (p : Pattern) (guard : d4985 p = 1) : d141 p ≤ (0 : Int) + d5074 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d141, d5074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d141, d5074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d141, d5074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12755 p hg
    simpa only [d141, d5074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12891 (p : Pattern) (guard : d4985 p = 1) : d1582 p ≤ (0 : Int) + d5075 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1582, d5075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12889 p hg
    simpa only [d1582, d5075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1582, d5075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12890 p hg
    simpa only [d1582, d5075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12892 (p : Pattern) (guard : d4985 p = 1) : d143 p ≤ (0 : Int) + d5076 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d143, d5076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d143, d5076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d143, d5076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12758 p hg
    simpa only [d143, d5076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12893 (p : Pattern) (guard : d4985 p = 1) : d144 p ≤ (0 : Int) + d5077 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d144, d5077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12892 p hg
    simpa only [d144, d5077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d144, d5077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d144, d5077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12894 (p : Pattern) (guard : d4985 p = 1) : d1583 p ≤ (0 : Int) + d5078 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1583, d5078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12891 p hg
    simpa only [d1583, d5078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1583, d5078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12893 p hg
    simpa only [d1583, d5078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12895 (p : Pattern) (guard : d4985 p = 1) : d139 p ≤ (0 : Int) + d139 p := by
  omega
theorem compare12896 (p : Pattern) (guard : d4985 p = 1) : d1584 p ≤ (0 : Int) + d5079 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1584, d5079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12877 p hg
    simpa only [d1584, d5079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1584, d5079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12895 p hg
    simpa only [d1584, d5079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12897 (p : Pattern) (guard : d4985 p = 1) : d141 p ≤ (0 : Int) + d141 p := by
  omega
theorem compare12898 (p : Pattern) (guard : d4985 p = 1) : d1585 p ≤ (0 : Int) + d5080 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1585, d5080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12896 p hg
    simpa only [d1585, d5080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1585, d5080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12897 p hg
    simpa only [d1585, d5080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12899 (p : Pattern) (guard : d4985 p = 1) : d144 p ≤ (0 : Int) + d144 p := by
  omega
theorem compare12900 (p : Pattern) (guard : d4985 p = 1) : d1586 p ≤ (0 : Int) + d5081 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1586, d5081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12898 p hg
    simpa only [d1586, d5081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1586, d5081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12899 p hg
    simpa only [d1586, d5081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12901 (p : Pattern) (guard : d4985 p = 1) : d1587 p ≤ (0 : Int) + d5082 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1587, d5082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12894 p hg
    simpa only [d1587, d5082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1587, d5082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12900 p hg
    simpa only [d1587, d5082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12902 (p : Pattern) (guard : d4985 p = 1) : d1588 p ≤ (0 : Int) + d5083 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1588, d5083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12883 p hg
    simpa only [d1588, d5083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1588, d5083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12901 p hg
    simpa only [d1588, d5083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12903 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1942 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12904 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5084 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d124, d5084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d124, d5084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d124, d5084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12903 p hg
    simpa only [d4985, d124, d5084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12905 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1951 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12906 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5085 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d124, d5085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d124, d5085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d124, d5085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12905 p hg
    simpa only [d4985, d124, d5085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12907 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5086 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12904 p hg
    simpa only [d5086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12906 p hg
    simpa only [d5086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12908 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1957 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12909 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5087 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d124, d5087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d124, d5087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d124, d5087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12908 p hg
    simpa only [d4985, d124, d5087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12910 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1966 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12911 (p : Pattern) (guard : d4985 p = 1) : d125 p ≤ (0 : Int) + d5088 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d125, d5088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d4985, d125, d5088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d125, d5088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12910 p hg
    simpa only [d4985, d125, d5088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12912 (p : Pattern) (guard : d4985 p = 1) : d126 p ≤ (0 : Int) + d5089 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d126, d5089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12909 p hg
    simpa only [d126, d5089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d126, d5089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12911 p hg
    simpa only [d126, d5089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12913 (p : Pattern) (guard : d4985 p = 1) : d1577 p ≤ (0 : Int) + d5090 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1577, d5090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12907 p hg
    simpa only [d1577, d5090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1577, d5090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12912 p hg
    simpa only [d1577, d5090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12914 (p : Pattern) (guard : d4985 p = 1) : d129 p ≤ (0 : Int) + d5091 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d129, d5091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12912 p hg
    simpa only [d129, d5091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d129, d5091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12871 p hg
    simpa only [d129, d5091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12915 (p : Pattern) (guard : d4985 p = 1) : d1578 p ≤ (0 : Int) + d5092 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1578, d5092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12913 p hg
    simpa only [d1578, d5092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1578, d5092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12914 p hg
    simpa only [d1578, d5092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12916 (p : Pattern) (guard : d4985 p = 1) : d139 p ≤ (0 : Int) + d5093 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d139, d5093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12886 p hg
    simpa only [d4985, d139, d5093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d139, d5093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12874 p hg
    simpa only [d4985, d139, d5093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12917 (p : Pattern) (guard : d4473 p = 1) : d120 p ≤ (0 : Int) + d120 p := by
  omega
theorem compare12918 (p : Pattern) (guard : d4985 p = 1) : d229 p ≤ (0 : Int) + d5094 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d229, d5094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12917 p hg
    simpa only [d4985, d229, d5094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d229, d5094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12876 p hg
    simpa only [d4985, d229, d5094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12919 (p : Pattern) (guard : d4985 p = 1) : d1053 p ≤ (0 : Int) + d5095 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1053, d5095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12916 p hg
    simpa only [d1053, d5095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1053, d5095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12918 p hg
    simpa only [d1053, d5095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12920 (p : Pattern) (guard : d4985 p = 1) : d1054 p ≤ (0 : Int) + d5096 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1054, d5096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12919 p hg
    simpa only [d1054, d5096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1054, d5096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1054, d5096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12921 (p : Pattern) (guard : d4985 p = 1) : d1589 p ≤ (0 : Int) + d5097 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1589, d5097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12920 p hg
    simpa only [d1589, d5097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1589, d5097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1589, d5097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12922 (p : Pattern) (guard : d4985 p = 1) : d1590 p ≤ (0 : Int) + d5098 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1590, d5098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12915 p hg
    simpa only [d1590, d5098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1590, d5098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12921 p hg
    simpa only [d1590, d5098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12923 (p : Pattern) (guard : d4985 p = 1) : d1584 p ≤ (0 : Int) + d5099 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1584, d5099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12906 p hg
    simpa only [d1584, d5099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1584, d5099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12916 p hg
    simpa only [d1584, d5099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12924 (p : Pattern) (guard : d4985 p = 1) : d141 p ≤ (0 : Int) + d5100 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d141, d5100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12911 p hg
    simpa only [d141, d5100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d141, d5100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12755 p hg
    simpa only [d141, d5100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12925 (p : Pattern) (guard : d4985 p = 1) : d1585 p ≤ (0 : Int) + d5101 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1585, d5101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12923 p hg
    simpa only [d1585, d5101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1585, d5101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12924 p hg
    simpa only [d1585, d5101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12926 (p : Pattern) (guard : d4985 p = 1) : d143 p ≤ (0 : Int) + d5102 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d143, d5102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12911 p hg
    simpa only [d143, d5102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d143, d5102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12758 p hg
    simpa only [d143, d5102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12927 (p : Pattern) (guard : d4985 p = 1) : d144 p ≤ (0 : Int) + d5103 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d144, d5103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12926 p hg
    simpa only [d144, d5103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d144, d5103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d144, d5103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12928 (p : Pattern) (guard : d4985 p = 1) : d1586 p ≤ (0 : Int) + d5104 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1586, d5104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12925 p hg
    simpa only [d1586, d5104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1586, d5104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12927 p hg
    simpa only [d1586, d5104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12929 (p : Pattern) (guard : d4985 p = 1) : d230 p ≤ (0 : Int) + d5105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d230, d5105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12918 p hg
    simpa only [d230, d5105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d230, d5105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d230, d5105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12930 (p : Pattern) (guard : d4985 p = 1) : d231 p ≤ (0 : Int) + d5106 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d231, d5106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12929 p hg
    simpa only [d231, d5106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d231, d5106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d231, d5106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12931 (p : Pattern) (guard : d4985 p = 1) : d1591 p ≤ (0 : Int) + d5107 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1591, d5107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12930 p hg
    simpa only [d1591, d5107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1591, d5107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1591, d5107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12932 (p : Pattern) (guard : d4985 p = 1) : d1592 p ≤ (0 : Int) + d5108 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1592, d5108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12928 p hg
    simpa only [d1592, d5108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1592, d5108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12931 p hg
    simpa only [d1592, d5108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12933 (p : Pattern) (guard : d4985 p = 1) : d1593 p ≤ (0 : Int) + d5109 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1593, d5109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12922 p hg
    simpa only [d1593, d5109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1593, d5109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12932 p hg
    simpa only [d1593, d5109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12934 (p : Pattern) (guard : d4985 p = 1) : d1594 p ≤ (0 : Int) + d5110 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1594, d5110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12902 p hg
    simpa only [d1594, d5110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1594, d5110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12933 p hg
    simpa only [d1594, d5110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12935 (p : Pattern) (guard : d4985 p = 1) : d1595 p ≤ (0 : Int) + d5111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1595, d5111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12871 p hg
    simpa only [d1595, d5111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1595, d5111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1595, d5111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12936 (p : Pattern) (guard : d4985 p = 1) : d1596 p ≤ (0 : Int) + d5112 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1596, d5112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12935 p hg
    simpa only [d1596, d5112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1596, d5112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1596, d5112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12937 (p : Pattern) (guard : d4985 p = 1) : d1597 p ≤ (0 : Int) + d5113 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1597, d5113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12936 p hg
    simpa only [d1597, d5113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1597, d5113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1597, d5113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12938 (p : Pattern) (guard : d4985 p = 1) : d1598 p ≤ (0 : Int) + d5114 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1598, d5114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12937 p hg
    simpa only [d1598, d5114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1598, d5114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1598, d5114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12939 (p : Pattern) (guard : d4985 p = 1) : d1599 p ≤ (0 : Int) + d5115 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1599, d5115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12933 p hg
    simpa only [d1599, d5115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1599, d5115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12938 p hg
    simpa only [d1599, d5115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12940 (p : Pattern) (guard : d4985 p = 1) : d1600 p ≤ (0 : Int) + d5116 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1600, d5116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12934 p hg
    simpa only [d1600, d5116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1600, d5116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12939 p hg
    simpa only [d1600, d5116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12941 (p : Pattern) (guard : d4985 p = 1) : d1601 p ≤ (0 : Int) + d5059 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12862 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12942 (p : Pattern) (guard : d4985 p = 1) : d1602 p ≤ (0 : Int) + d5062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1602, d5062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12941 p hg
    simpa only [d1602, d5062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1602, d5062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d1602, d5062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12943 (p : Pattern) (guard : d4985 p = 1) : d1603 p ≤ (0 : Int) + d5065 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1603, d5065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12942 p hg
    simpa only [d1603, d5065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1603, d5065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12872 p hg
    simpa only [d1603, d5065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12944 (p : Pattern) (guard : d4985 p = 1) : d1604 p ≤ (0 : Int) + d5071 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1604, d5071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12943 p hg
    simpa only [d1604, d5071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1604, d5071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12882 p hg
    simpa only [d1604, d5071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12945 (p : Pattern) (guard : d4985 p = 1) : d1584 p ≤ (0 : Int) + d5073 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1584, d5073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d1584, d5073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1584, d5073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12888 p hg
    simpa only [d1584, d5073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12946 (p : Pattern) (guard : d4985 p = 1) : d1585 p ≤ (0 : Int) + d5075 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1585, d5075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12945 p hg
    simpa only [d1585, d5075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1585, d5075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12890 p hg
    simpa only [d1585, d5075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12947 (p : Pattern) (guard : d4985 p = 1) : d1586 p ≤ (0 : Int) + d5078 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1586, d5078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12946 p hg
    simpa only [d1586, d5078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1586, d5078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12893 p hg
    simpa only [d1586, d5078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12948 (p : Pattern) (guard : d4985 p = 1) : d1586 p ≤ (0 : Int) + d5082 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12947 p hg
    simpa only [d5082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12900 p hg
    simpa only [d5082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12949 (p : Pattern) (guard : d4985 p = 1) : d1605 p ≤ (0 : Int) + d5083 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1605, d5083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12944 p hg
    simpa only [d1605, d5083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1605, d5083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12948 p hg
    simpa only [d1605, d5083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12950 (p : Pattern) (guard : d4985 p = 1) : d1606 p ≤ (0 : Int) + d5110 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1606, d5110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12949 p hg
    simpa only [d1606, d5110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1606, d5110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12933 p hg
    simpa only [d1606, d5110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12951 (p : Pattern) (guard : d4985 p = 1) : d1607 p ≤ (0 : Int) + d5117 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1607, d5117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12933 p hg
    simpa only [d1607, d5117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1607, d5117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1607, d5117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12952 (p : Pattern) (guard : d4985 p = 1) : d1608 p ≤ (0 : Int) + d5118 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1608, d5118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12950 p hg
    simpa only [d1608, d5118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1608, d5118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12951 p hg
    simpa only [d1608, d5118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12953 (p : Pattern) (guard : d4985 p = 1) : d1609 p ≤ (0 : Int) + d5119 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1609, d5119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12940 p hg
    simpa only [d1609, d5119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1609, d5119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12952 p hg
    simpa only [d1609, d5119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12954 (p : Pattern) (guard : d4985 p = 1) : d1610 p ≤ (0 : Int) + d5120 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1610, d5120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12834 p hg
    simpa only [d1610, d5120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1610, d5120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12953 p hg
    simpa only [d1610, d5120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12955 (p : Pattern) (guard : d4985 p = 1) : d1611 p ≤ (0 : Int) + d5121 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1611, d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12857 p hg
    simpa only [d1611, d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1611, d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12954 p hg
    simpa only [d1611, d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12956 (p : Pattern) (guard : d4985 p = 1) : d1529 p ≤ (0 : Int) + d5017 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12806 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12771 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12957 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2012 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12958 (p : Pattern) (guard : d4985 p = 1) : d43 p ≤ (0 : Int) + d5122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d43, d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12717 p hg
    simpa only [d4985, d43, d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d43, d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12957 p hg
    simpa only [d4985, d43, d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12959 (p : Pattern) (guard : d4985 p = 1) : d47 p ≤ (0 : Int) + d5123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d47, d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12771 p hg
    simpa only [d47, d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d47, d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12958 p hg
    simpa only [d47, d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12960 (p : Pattern) (guard : d4985 p = 1) : d1530 p ≤ (0 : Int) + d5124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1530, d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12956 p hg
    simpa only [d1530, d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1530, d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12959 p hg
    simpa only [d1530, d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12961 (p : Pattern) (guard : d4985 p = 1) : d50 p ≤ (0 : Int) + d5125 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d50, d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12959 p hg
    simpa only [d50, d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d50, d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12783 p hg
    simpa only [d50, d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12962 (p : Pattern) (guard : d4985 p = 1) : d1531 p ≤ (0 : Int) + d5126 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1531, d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12960 p hg
    simpa only [d1531, d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1531, d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12961 p hg
    simpa only [d1531, d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12963 (p : Pattern) (guard : d4985 p = 1) : d66 p ≤ (0 : Int) + d5127 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d66, d5127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12747 p hg
    simpa only [d4985, d66, d5127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d66, d5127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12734 p hg
    simpa only [d4985, d66, d5127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12964 (p : Pattern) (guard : d4985 p = 1) : d66 p ≤ (0 : Int) + d5128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12963 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12965 (p : Pattern) (guard : d4985 p = 1) : d66 p ≤ (0 : Int) + d5129 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d66, d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12747 p hg
    simpa only [d4985, d66, d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d66, d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12737 p hg
    simpa only [d4985, d66, d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12966 (p : Pattern) (guard : d4985 p = 1) : d173 p ≤ (0 : Int) + d173 p := by
  omega
theorem compare12967 (p : Pattern) (guard : d4985 p = 1) : d176 p ≤ (0 : Int) + d5130 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d176, d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12965 p hg
    simpa only [d176, d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d176, d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12966 p hg
    simpa only [d176, d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12968 (p : Pattern) (guard : d4985 p = 1) : d1612 p ≤ (0 : Int) + d5131 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1612, d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12964 p hg
    simpa only [d1612, d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1612, d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12967 p hg
    simpa only [d1612, d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12969 (p : Pattern) (guard : d4985 p = 1) : d177 p ≤ (0 : Int) + d177 p := by
  omega
theorem compare12970 (p : Pattern) (guard : d4985 p = 1) : d1613 p ≤ (0 : Int) + d5132 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1613, d5132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12968 p hg
    simpa only [d1613, d5132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1613, d5132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12969 p hg
    simpa only [d1613, d5132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12971 (p : Pattern) (guard : d4985 p = 1) : d1614 p ≤ (0 : Int) + d5133 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1614, d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12962 p hg
    simpa only [d1614, d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1614, d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12970 p hg
    simpa only [d1614, d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12972 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2030 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12973 (p : Pattern) (guard : d4985 p = 1) : d66 p ≤ (0 : Int) + d5134 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d66, d5134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12747 p hg
    simpa only [d4985, d66, d5134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d66, d5134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12972 p hg
    simpa only [d4985, d66, d5134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12974 (p : Pattern) (guard : d4985 p = 1) : d1518 p ≤ (0 : Int) + d5135 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1518, d5135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12771 p hg
    simpa only [d1518, d5135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1518, d5135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12973 p hg
    simpa only [d1518, d5135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12975 (p : Pattern) (guard : d4985 p = 1) : d68 p ≤ (0 : Int) + d5136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d68, d5136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12958 p hg
    simpa only [d68, d5136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d68, d5136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12782 p hg
    simpa only [d68, d5136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12976 (p : Pattern) (guard : d4985 p = 1) : d1519 p ≤ (0 : Int) + d5137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1519, d5137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12974 p hg
    simpa only [d1519, d5137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1519, d5137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12975 p hg
    simpa only [d1519, d5137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12977 (p : Pattern) (guard : d4985 p = 1) : d71 p ≤ (0 : Int) + d5138 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d71, d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12958 p hg
    simpa only [d71, d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d71, d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12755 p hg
    simpa only [d71, d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12978 (p : Pattern) (guard : d4985 p = 1) : d74 p ≤ (0 : Int) + d5139 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d74, d5139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12977 p hg
    simpa only [d74, d5139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d74, d5139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12759 p hg
    simpa only [d74, d5139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12979 (p : Pattern) (guard : d4985 p = 1) : d1520 p ≤ (0 : Int) + d5140 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1520, d5140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12976 p hg
    simpa only [d1520, d5140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1520, d5140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12978 p hg
    simpa only [d1520, d5140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12980 (p : Pattern) (guard : d4985 p = 1) : d1615 p ≤ (0 : Int) + d5141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1615, d5141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12963 p hg
    simpa only [d1615, d5141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1615, d5141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12739 p hg
    simpa only [d1615, d5141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12981 (p : Pattern) (guard : d4985 p = 1) : d181 p ≤ (0 : Int) + d181 p := by
  omega
theorem compare12982 (p : Pattern) (guard : d4985 p = 1) : d1616 p ≤ (0 : Int) + d5142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1616, d5142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12980 p hg
    simpa only [d1616, d5142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1616, d5142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12981 p hg
    simpa only [d1616, d5142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12983 (p : Pattern) (guard : d4985 p = 1) : d184 p ≤ (0 : Int) + d184 p := by
  omega
theorem compare12984 (p : Pattern) (guard : d4985 p = 1) : d1617 p ≤ (0 : Int) + d5143 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1617, d5143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12982 p hg
    simpa only [d1617, d5143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1617, d5143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12983 p hg
    simpa only [d1617, d5143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12985 (p : Pattern) (guard : d4985 p = 1) : d1618 p ≤ (0 : Int) + d5144 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1618, d5144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12979 p hg
    simpa only [d1618, d5144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1618, d5144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12984 p hg
    simpa only [d1618, d5144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12986 (p : Pattern) (guard : d4985 p = 1) : d1619 p ≤ (0 : Int) + d5145 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1619, d5145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12971 p hg
    simpa only [d1619, d5145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1619, d5145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12985 p hg
    simpa only [d1619, d5145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12987 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2048 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12988 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d5146 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d46, d5146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d46, d5146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d46, d5146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12987 p hg
    simpa only [d4985, d46, d5146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12989 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2054 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12990 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d5147 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d46, d5147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d46, d5147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d46, d5147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12989 p hg
    simpa only [d4985, d46, d5147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12991 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d5148 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12988 p hg
    simpa only [d5148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12990 p hg
    simpa only [d5148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12992 (p : Pattern) (guard : d4985 p = 1) : d1620 p ≤ (0 : Int) + d5149 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1620, d5149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12991 p hg
    simpa only [d1620, d5149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1620, d5149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d1620, d5149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12993 (p : Pattern) (guard : d4985 p = 1) : d1621 p ≤ (0 : Int) + d5150 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1621, d5150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12992 p hg
    simpa only [d1621, d5150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1621, d5150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d1621, d5150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12994 (p : Pattern) (guard : d4473 p = 1) : d191 p ≤ (0 : Int) + d191 p := by
  omega
theorem compare12995 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2061 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12996 (p : Pattern) (guard : d4985 p = 1) : d1622 p ≤ (0 : Int) + d5151 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1622, d5151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12994 p hg
    simpa only [d4985, d1622, d5151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1622, d5151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12995 p hg
    simpa only [d4985, d1622, d5151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12997 (p : Pattern) (guard : d4985 p = 1) : d1623 p ≤ (0 : Int) + d5152 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1623, d5152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12778 p hg
    simpa only [d1623, d5152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1623, d5152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12996 p hg
    simpa only [d1623, d5152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12998 (p : Pattern) (guard : d4985 p = 1) : d1624 p ≤ (0 : Int) + d5153 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1624, d5153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12997 p hg
    simpa only [d1624, d5153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1624, d5153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1624, d5153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12999 (p : Pattern) (guard : d4985 p = 1) : d1625 p ≤ (0 : Int) + d5154 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1625, d5154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12998 p hg
    simpa only [d1625, d5154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1625, d5154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1625, d5154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13000 (p : Pattern) (guard : d4985 p = 1) : d1626 p ≤ (0 : Int) + d5155 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1626, d5155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12993 p hg
    simpa only [d1626, d5155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1626, d5155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12999 p hg
    simpa only [d1626, d5155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13001 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2071 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13002 (p : Pattern) (guard : d4985 p = 1) : d66 p ≤ (0 : Int) + d5156 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d66, d5156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12747 p hg
    simpa only [d4985, d66, d5156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d66, d5156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13001 p hg
    simpa only [d4985, d66, d5156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13003 (p : Pattern) (guard : d4985 p = 1) : d66 p ≤ (0 : Int) + d5157 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13002 p hg
    simpa only [d5157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d5157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13004 (p : Pattern) (guard : d4985 p = 1) : d1627 p ≤ (0 : Int) + d5158 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1627, d5158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12778 p hg
    simpa only [d1627, d5158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1627, d5158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12758 p hg
    simpa only [d1627, d5158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13005 (p : Pattern) (guard : d4985 p = 1) : d1628 p ≤ (0 : Int) + d5159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1628, d5159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13003 p hg
    simpa only [d1628, d5159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1628, d5159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13004 p hg
    simpa only [d1628, d5159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13006 (p : Pattern) (guard : d4985 p = 1) : d1629 p ≤ (0 : Int) + d5160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1629, d5160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13005 p hg
    simpa only [d1629, d5160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1629, d5160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12800 p hg
    simpa only [d1629, d5160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13007 (p : Pattern) (guard : d4985 p = 1) : d1630 p ≤ (0 : Int) + d5161 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1630, d5161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12996 p hg
    simpa only [d1630, d5161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1630, d5161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1630, d5161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13008 (p : Pattern) (guard : d4985 p = 1) : d1631 p ≤ (0 : Int) + d5162 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1631, d5162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13007 p hg
    simpa only [d1631, d5162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1631, d5162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1631, d5162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13009 (p : Pattern) (guard : d4985 p = 1) : d1632 p ≤ (0 : Int) + d5163 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1632, d5163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13008 p hg
    simpa only [d1632, d5163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1632, d5163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1632, d5163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13010 (p : Pattern) (guard : d4985 p = 1) : d1633 p ≤ (0 : Int) + d5164 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1633, d5164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13006 p hg
    simpa only [d1633, d5164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1633, d5164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13009 p hg
    simpa only [d1633, d5164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13011 (p : Pattern) (guard : d4985 p = 1) : d1634 p ≤ (0 : Int) + d5165 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1634, d5165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13000 p hg
    simpa only [d1634, d5165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1634, d5165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13010 p hg
    simpa only [d1634, d5165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13012 (p : Pattern) (guard : d4985 p = 1) : d1635 p ≤ (0 : Int) + d5166 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1635, d5166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12986 p hg
    simpa only [d1635, d5166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1635, d5166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13011 p hg
    simpa only [d1635, d5166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13013 (p : Pattern) (guard : d4985 p = 1) : d1636 p ≤ (0 : Int) + d5167 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1636, d5167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13011 p hg
    simpa only [d1636, d5167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1636, d5167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1636, d5167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13014 (p : Pattern) (guard : d4985 p = 1) : d1637 p ≤ (0 : Int) + d5168 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1637, d5168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13012 p hg
    simpa only [d1637, d5168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1637, d5168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13013 p hg
    simpa only [d1637, d5168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13015 (p : Pattern) (guard : d4985 p = 1) : d1638 p ≤ (0 : Int) + d5169 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1638, d5169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12848 p hg
    simpa only [d1638, d5169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1638, d5169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13014 p hg
    simpa only [d1638, d5169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13016 (p : Pattern) (guard : d4985 p = 1) : d1639 p ≤ (0 : Int) + d5170 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1639, d5170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12834 p hg
    simpa only [d1639, d5170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1639, d5170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13015 p hg
    simpa only [d1639, d5170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13017 (p : Pattern) (guard : d4985 p = 1) : d215 p ≤ (0 : Int) + d5171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d215, d5171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d215, d5171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d215, d5171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d215, d5171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13018 (p : Pattern) (guard : d4985 p = 1) : d1640 p ≤ (0 : Int) + d5172 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1640, d5172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12889 p hg
    simpa only [d1640, d5172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1640, d5172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13017 p hg
    simpa only [d1640, d5172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13019 (p : Pattern) (guard : d4985 p = 1) : d217 p ≤ (0 : Int) + d5173 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d217, d5173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13017 p hg
    simpa only [d217, d5173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d217, d5173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d217, d5173, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
