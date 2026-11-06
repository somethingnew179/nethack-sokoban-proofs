/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons093
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13160 (p : Pattern) (guard : d4206 p = 1) : d1053 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1053, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11975 p hg
    simpa only [d1053, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1053, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12069 p hg
    simpa only [d1053, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13161 (p : Pattern) (guard : d4206 p = 1) : d1054 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1054, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13160 p hg
    simpa only [d1054, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1054, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1054, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13162 (p : Pattern) (guard : d4206 p = 1) : d1589 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1589, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13161 p hg
    simpa only [d1589, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1589, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1589, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13163 (p : Pattern) (guard : d4206 p = 1) : d1590 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1590, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11986 p hg
    simpa only [d1590, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1590, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13162 p hg
    simpa only [d1590, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13164 (p : Pattern) (guard : d4206 p = 1) : d1591 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1591, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12071 p hg
    simpa only [d1591, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1591, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1591, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13165 (p : Pattern) (guard : d4206 p = 1) : d1592 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1592, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11991 p hg
    simpa only [d1592, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1592, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13164 p hg
    simpa only [d1592, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13166 (p : Pattern) (guard : d4206 p = 1) : d1593 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1593, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13163 p hg
    simpa only [d1593, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1593, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13165 p hg
    simpa only [d1593, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13167 (p : Pattern) (guard : d4206 p = 1) : d1594 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1594, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13159 p hg
    simpa only [d1594, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1594, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13166 p hg
    simpa only [d1594, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13168 (p : Pattern) (guard : d4206 p = 1) : d1597 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12000 p hg
    simpa only [d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13169 (p : Pattern) (guard : d4206 p = 1) : d1598 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13168 p hg
    simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13170 (p : Pattern) (guard : d4206 p = 1) : d1599 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1599, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13166 p hg
    simpa only [d1599, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1599, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13169 p hg
    simpa only [d1599, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13171 (p : Pattern) (guard : d4206 p = 1) : d1600 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1600, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13167 p hg
    simpa only [d1600, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1600, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13170 p hg
    simpa only [d1600, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13172 (p : Pattern) (guard : d4206 p = 1) : d1604 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1604, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12007 p hg
    simpa only [d1604, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1604, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13153 p hg
    simpa only [d1604, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13173 (p : Pattern) (guard : d4206 p = 1) : d1586 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11991 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13157 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13174 (p : Pattern) (guard : d4206 p = 1) : d1605 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1605, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13172 p hg
    simpa only [d1605, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1605, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13173 p hg
    simpa only [d1605, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13175 (p : Pattern) (guard : d4206 p = 1) : d1606 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1606, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13174 p hg
    simpa only [d1606, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1606, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13166 p hg
    simpa only [d1606, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13176 (p : Pattern) (guard : d4206 p = 1) : d1607 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1607, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13166 p hg
    simpa only [d1607, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1607, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1607, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13177 (p : Pattern) (guard : d4206 p = 1) : d1608 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1608, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13175 p hg
    simpa only [d1608, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1608, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13176 p hg
    simpa only [d1608, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13178 (p : Pattern) (guard : d4206 p = 1) : d1609 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1609, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13171 p hg
    simpa only [d1609, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1609, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13177 p hg
    simpa only [d1609, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13179 (p : Pattern) (guard : d4206 p = 1) : d1610 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1610, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13136 p hg
    simpa only [d1610, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1610, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13178 p hg
    simpa only [d1610, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13180 (p : Pattern) (guard : d4206 p = 1) : d1611 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1611, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13148 p hg
    simpa only [d1611, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1611, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13179 p hg
    simpa only [d1611, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13181 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (0 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4206, d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3074 p hg
    simpa only [d4206, d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13182 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (0 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11878 p hg
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13181 p hg
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13183 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (0 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4206, d66, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2944 p hg
    simpa only [d4206, d66, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13184 (p : Pattern) (guard : d4206 p = 1) : d176 p ≤ (0 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d176, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13183 p hg
    simpa only [d176, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d176, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5235 p hg
    simpa only [d176, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13185 (p : Pattern) (guard : d4206 p = 1) : d1612 p ≤ (0 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1612, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13182 p hg
    simpa only [d1612, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1612, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13184 p hg
    simpa only [d1612, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13186 (p : Pattern) (guard : d4206 p = 1) : d1613 p ≤ (0 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1613, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13185 p hg
    simpa only [d1613, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1613, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5238 p hg
    simpa only [d1613, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13187 (p : Pattern) (guard : d4206 p = 1) : d1614 p ≤ (0 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1614, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11904 p hg
    simpa only [d1614, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1614, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13186 p hg
    simpa only [d1614, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13188 (p : Pattern) (guard : d4206 p = 1) : d1615 p ≤ (0 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1615, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13181 p hg
    simpa only [d1615, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1615, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d1615, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13189 (p : Pattern) (guard : d4206 p = 1) : d1616 p ≤ (0 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1616, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13188 p hg
    simpa only [d1616, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1616, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5242 p hg
    simpa only [d1616, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13190 (p : Pattern) (guard : d4206 p = 1) : d1617 p ≤ (0 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1617, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13189 p hg
    simpa only [d1617, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1617, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5244 p hg
    simpa only [d1617, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13191 (p : Pattern) (guard : d4206 p = 1) : d1618 p ≤ (0 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1618, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11897 p hg
    simpa only [d1618, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1618, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13190 p hg
    simpa only [d1618, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13192 (p : Pattern) (guard : d4206 p = 1) : d1619 p ≤ (0 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1619, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13187 p hg
    simpa only [d1619, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1619, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13191 p hg
    simpa only [d1619, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13193 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d192 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13194 (p : Pattern) (guard : d4206 p = 1) : d1622 p ≤ (0 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1622, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d4206, d1622, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1622, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13193 p hg
    simpa only [d4206, d1622, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13195 (p : Pattern) (guard : d4206 p = 1) : d1623 p ≤ (0 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1623, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11865 p hg
    simpa only [d1623, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1623, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13194 p hg
    simpa only [d1623, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13196 (p : Pattern) (guard : d4206 p = 1) : d1624 p ≤ (0 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1624, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13195 p hg
    simpa only [d1624, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1624, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1624, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13197 (p : Pattern) (guard : d4206 p = 1) : d1625 p ≤ (0 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1625, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13196 p hg
    simpa only [d1625, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1625, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1625, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13198 (p : Pattern) (guard : d4206 p = 1) : d1626 p ≤ (0 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1626, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12028 p hg
    simpa only [d1626, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1626, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13197 p hg
    simpa only [d1626, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13199 (p : Pattern) (guard : d4206 p = 1) : d1630 p ≤ (0 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1630, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13194 p hg
    simpa only [d1630, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1630, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1630, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13200 (p : Pattern) (guard : d4206 p = 1) : d1631 p ≤ (0 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1631, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13199 p hg
    simpa only [d1631, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1631, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1631, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13201 (p : Pattern) (guard : d4206 p = 1) : d1632 p ≤ (0 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1632, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13200 p hg
    simpa only [d1632, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1632, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1632, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13202 (p : Pattern) (guard : d4206 p = 1) : d1633 p ≤ (0 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1633, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12035 p hg
    simpa only [d1633, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1633, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13201 p hg
    simpa only [d1633, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13203 (p : Pattern) (guard : d4206 p = 1) : d1634 p ≤ (0 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1634, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13198 p hg
    simpa only [d1634, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1634, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13202 p hg
    simpa only [d1634, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13204 (p : Pattern) (guard : d4206 p = 1) : d1635 p ≤ (0 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1635, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13192 p hg
    simpa only [d1635, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1635, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13203 p hg
    simpa only [d1635, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13205 (p : Pattern) (guard : d4206 p = 1) : d1636 p ≤ (0 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1636, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13203 p hg
    simpa only [d1636, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1636, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1636, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13206 (p : Pattern) (guard : d4206 p = 1) : d1637 p ≤ (0 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1637, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13204 p hg
    simpa only [d1637, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1637, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13205 p hg
    simpa only [d1637, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13207 (p : Pattern) (guard : d4206 p = 1) : d1638 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1638, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13142 p hg
    simpa only [d1638, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1638, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13206 p hg
    simpa only [d1638, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13208 (p : Pattern) (guard : d4206 p = 1) : d1639 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1639, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13136 p hg
    simpa only [d1639, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1639, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13207 p hg
    simpa only [d1639, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13209 (p : Pattern) (guard : d4206 p = 1) : d1642 p ≤ (0 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1642, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13155 p hg
    simpa only [d1642, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1642, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5274 p hg
    simpa only [d1642, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13210 (p : Pattern) (guard : d4206 p = 1) : d1643 p ≤ (0 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1643, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13209 p hg
    simpa only [d1643, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1643, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5276 p hg
    simpa only [d1643, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13211 (p : Pattern) (guard : d4206 p = 1) : d1644 p ≤ (0 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1644, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12047 p hg
    simpa only [d1644, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1644, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13210 p hg
    simpa only [d1644, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13212 (p : Pattern) (guard : d4206 p = 1) : d1645 p ≤ (0 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1645, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13154 p hg
    simpa only [d1645, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1645, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13211 p hg
    simpa only [d1645, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13213 (p : Pattern) (guard : d4206 p = 1) : d1646 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1646, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12052 p hg
    simpa only [d1646, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1646, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13164 p hg
    simpa only [d1646, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13214 (p : Pattern) (guard : d4206 p = 1) : d1647 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1647, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13163 p hg
    simpa only [d1647, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1647, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13213 p hg
    simpa only [d1647, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13215 (p : Pattern) (guard : d4206 p = 1) : d1648 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1648, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13212 p hg
    simpa only [d1648, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1648, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13214 p hg
    simpa only [d1648, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13216 (p : Pattern) (guard : d4206 p = 1) : d1649 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1649, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13214 p hg
    simpa only [d1649, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1649, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13169 p hg
    simpa only [d1649, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13217 (p : Pattern) (guard : d4206 p = 1) : d1650 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1650, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13215 p hg
    simpa only [d1650, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1650, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13216 p hg
    simpa only [d1650, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13218 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (0 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d139, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4206, d139, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d139, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3161 p hg
    simpa only [d4206, d139, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13219 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (0 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11975 p hg
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13218 p hg
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13220 (p : Pattern) (guard : d4206 p = 1) : d1651 p ≤ (0 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1651, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13219 p hg
    simpa only [d1651, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1651, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5274 p hg
    simpa only [d1651, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13221 (p : Pattern) (guard : d4206 p = 1) : d1652 p ≤ (0 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1652, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13220 p hg
    simpa only [d1652, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1652, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d1652, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13222 (p : Pattern) (guard : d4206 p = 1) : d1653 p ≤ (0 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1653, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12007 p hg
    simpa only [d1653, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1653, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13221 p hg
    simpa only [d1653, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13223 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (0 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d125, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4206, d125, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d125, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3161 p hg
    simpa only [d4206, d125, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13224 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (0 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13223 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5294 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13225 (p : Pattern) (guard : d4206 p = 1) : d1654 p ≤ (0 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1654, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13224 p hg
    simpa only [d1654, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1654, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5296 p hg
    simpa only [d1654, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13226 (p : Pattern) (guard : d4206 p = 1) : d1655 p ≤ (0 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1655, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13225 p hg
    simpa only [d1655, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1655, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5298 p hg
    simpa only [d1655, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13227 (p : Pattern) (guard : d4206 p = 1) : d1656 p ≤ (0 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1656, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12052 p hg
    simpa only [d1656, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1656, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13226 p hg
    simpa only [d1656, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13228 (p : Pattern) (guard : d4206 p = 1) : d1657 p ≤ (0 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1657, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13222 p hg
    simpa only [d1657, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1657, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13227 p hg
    simpa only [d1657, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13229 (p : Pattern) (guard : d4206 p = 1) : d1661 p ≤ (0 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1661, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12066 p hg
    simpa only [d1661, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1661, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13164 p hg
    simpa only [d1661, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13230 (p : Pattern) (guard : d4206 p = 1) : d237 p ≤ (0 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d237, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11871 p hg
    simpa only [d237, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d237, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d237, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13231 (p : Pattern) (guard : d4206 p = 1) : d1662 p ≤ (0 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1662, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13230 p hg
    simpa only [d1662, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1662, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1662, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13232 (p : Pattern) (guard : d4206 p = 1) : d1663 p ≤ (0 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1663, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12072 p hg
    simpa only [d1663, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1663, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13231 p hg
    simpa only [d1663, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13233 (p : Pattern) (guard : d4206 p = 1) : d1664 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1664, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13229 p hg
    simpa only [d1664, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1664, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13232 p hg
    simpa only [d1664, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13234 (p : Pattern) (guard : d4206 p = 1) : d1665 p ≤ (0 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1665, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13228 p hg
    simpa only [d1665, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1665, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13233 p hg
    simpa only [d1665, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13235 (p : Pattern) (guard : d4206 p = 1) : d1671 p ≤ (0 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1671, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12069 p hg
    simpa only [d1671, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1671, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11884 p hg
    simpa only [d1671, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13236 (p : Pattern) (guard : d4206 p = 1) : d1672 p ≤ (0 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1672, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13235 p hg
    simpa only [d1672, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1672, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1672, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13237 (p : Pattern) (guard : d4206 p = 1) : d1673 p ≤ (0 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1673, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13236 p hg
    simpa only [d1673, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1673, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1673, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13238 (p : Pattern) (guard : d4206 p = 1) : d1674 p ≤ (0 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1674, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12081 p hg
    simpa only [d1674, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1674, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13237 p hg
    simpa only [d1674, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13239 (p : Pattern) (guard : d4206 p = 1) : d1675 p ≤ (0 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1675, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13238 p hg
    simpa only [d1675, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1675, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13232 p hg
    simpa only [d1675, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13240 (p : Pattern) (guard : d4206 p = 1) : d1676 p ≤ (0 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1676, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13239 p hg
    simpa only [d1676, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1676, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1676, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13241 (p : Pattern) (guard : d4206 p = 1) : d1677 p ≤ (0 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1677, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13234 p hg
    simpa only [d1677, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1677, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13240 p hg
    simpa only [d1677, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13242 (p : Pattern) (guard : d4206 p = 1) : d1678 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1678, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13217 p hg
    simpa only [d1678, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1678, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13241 p hg
    simpa only [d1678, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13243 (p : Pattern) (guard : d4206 p = 1) : d1679 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1679, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13136 p hg
    simpa only [d1679, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1679, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13242 p hg
    simpa only [d1679, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13244 (p : Pattern) (guard : d4206 p = 1) : d1680 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1680, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13208 p hg
    simpa only [d1680, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1680, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13243 p hg
    simpa only [d1680, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13245 (p : Pattern) (guard : d4206 p = 1) : d1681 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1681, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13180 p hg
    simpa only [d1681, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1681, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13244 p hg
    simpa only [d1681, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13246 (p : Pattern) (guard : d0 p = 1) : d324 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13247 (p : Pattern) (guard : d4206 p = 1) : d1504 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1504, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4206, d1504, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1504, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13246 p hg
    simpa only [d4206, d1504, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13248 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13249 (p : Pattern) (guard : d4206 p = 1) : d1505 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1505, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4206, d1505, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1505, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13248 p hg
    simpa only [d4206, d1505, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13250 (p : Pattern) (guard : d4206 p = 1) : d1506 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13247 p hg
    simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13249 p hg
    simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13251 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13252 (p : Pattern) (guard : d4206 p = 1) : d1507 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1507, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4206, d1507, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1507, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13251 p hg
    simpa only [d4206, d1507, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13253 (p : Pattern) (guard : d4206 p = 1) : d1508 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1508, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13252 p hg
    simpa only [d1508, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1508, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12095 p hg
    simpa only [d1508, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13254 (p : Pattern) (guard : d4206 p = 1) : d1509 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1509, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13250 p hg
    simpa only [d1509, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1509, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13253 p hg
    simpa only [d1509, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13255 (p : Pattern) (guard : d4206 p = 1) : d1510 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1510, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13254 p hg
    simpa only [d1510, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1510, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12103 p hg
    simpa only [d1510, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13256 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (2 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4206, d46, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12107 p hg
    simpa only [d4206, d46, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13257 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (2 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4206, d46, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12253 p hg
    simpa only [d4206, d46, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13258 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (2 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13256 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13257 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13259 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (2 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4206, d46, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12116 p hg
    simpa only [d4206, d46, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13260 (p : Pattern) (guard : d4206 p = 1) : d43 p ≤ (2 : Int) + d43 p := by
  omega
theorem compare13261 (p : Pattern) (guard : d4206 p = 1) : d47 p ≤ (2 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d47, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13259 p hg
    simpa only [d47, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d47, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13260 p hg
    simpa only [d47, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13262 (p : Pattern) (guard : d4206 p = 1) : d1511 p ≤ (2 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1511, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13258 p hg
    simpa only [d1511, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1511, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13261 p hg
    simpa only [d1511, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13263 (p : Pattern) (guard : d4206 p = 1) : d50 p ≤ (2 : Int) + d50 p := by
  omega
theorem compare13264 (p : Pattern) (guard : d4206 p = 1) : d1512 p ≤ (2 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1512, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13262 p hg
    simpa only [d1512, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1512, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13263 p hg
    simpa only [d1512, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13265 (p : Pattern) (guard : d4206 p = 1) : d1513 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1513, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13255 p hg
    simpa only [d1513, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1513, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13264 p hg
    simpa only [d1513, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13266 (p : Pattern) (guard : d0 p = 1) : d359 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13267 (p : Pattern) (guard : d4206 p = 1) : d1514 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1514, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4206, d1514, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1514, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13266 p hg
    simpa only [d4206, d1514, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13268 (p : Pattern) (guard : d4206 p = 1) : d1515 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1515, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13267 p hg
    simpa only [d1515, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1515, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12108 p hg
    simpa only [d1515, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13269 (p : Pattern) (guard : d4206 p = 1) : d1516 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1516, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13268 p hg
    simpa only [d1516, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1516, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12110 p hg
    simpa only [d1516, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13270 (p : Pattern) (guard : d4206 p = 1) : d1517 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1517, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13269 p hg
    simpa only [d1517, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1517, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12119 p hg
    simpa only [d1517, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13271 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare13272 (p : Pattern) (guard : d4206 p = 1) : d1518 p ≤ (2 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1518, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13257 p hg
    simpa only [d1518, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1518, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13271 p hg
    simpa only [d1518, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13273 (p : Pattern) (guard : d4206 p = 1) : d68 p ≤ (2 : Int) + d68 p := by
  omega
theorem compare13274 (p : Pattern) (guard : d4206 p = 1) : d1519 p ≤ (2 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1519, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13272 p hg
    simpa only [d1519, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1519, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13273 p hg
    simpa only [d1519, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13275 (p : Pattern) (guard : d4206 p = 1) : d74 p ≤ (2 : Int) + d74 p := by
  omega
theorem compare13276 (p : Pattern) (guard : d4206 p = 1) : d1520 p ≤ (2 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1520, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13274 p hg
    simpa only [d1520, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1520, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13275 p hg
    simpa only [d1520, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13277 (p : Pattern) (guard : d4206 p = 1) : d1521 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1521, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13270 p hg
    simpa only [d1521, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1521, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13276 p hg
    simpa only [d1521, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13278 (p : Pattern) (guard : d4206 p = 1) : d1522 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1522, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13265 p hg
    simpa only [d1522, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1522, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13277 p hg
    simpa only [d1522, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13279 (p : Pattern) (guard : d4206 p = 1) : d1523 p ≤ (2 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1523, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12257 p hg
    simpa only [d1523, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1523, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1523, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13280 (p : Pattern) (guard : d4206 p = 1) : d1524 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1524, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12104 p hg
    simpa only [d1524, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1524, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13279 p hg
    simpa only [d1524, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13281 (p : Pattern) (guard : d4206 p = 1) : d1525 p ≤ (2 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1525, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12267 p hg
    simpa only [d1525, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1525, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1525, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13282 (p : Pattern) (guard : d4206 p = 1) : d1526 p ≤ (2 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1526, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12120 p hg
    simpa only [d1526, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1526, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13281 p hg
    simpa only [d1526, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13283 (p : Pattern) (guard : d4206 p = 1) : d1527 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1527, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13280 p hg
    simpa only [d1527, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1527, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13282 p hg
    simpa only [d1527, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13284 (p : Pattern) (guard : d4206 p = 1) : d1528 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1528, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13278 p hg
    simpa only [d1528, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1528, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13283 p hg
    simpa only [d1528, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13285 (p : Pattern) (guard : d4206 p = 1) : d1529 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13252 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12093 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13286 (p : Pattern) (guard : d4206 p = 1) : d1530 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1530, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13285 p hg
    simpa only [d1530, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1530, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12096 p hg
    simpa only [d1530, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13287 (p : Pattern) (guard : d4206 p = 1) : d1531 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1531, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13286 p hg
    simpa only [d1531, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1531, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12103 p hg
    simpa only [d1531, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13288 (p : Pattern) (guard : d4206 p = 1) : d1532 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1532, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13287 p hg
    simpa only [d1532, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1532, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13279 p hg
    simpa only [d1532, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13289 (p : Pattern) (guard : d4206 p = 1) : d1533 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1533, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13288 p hg
    simpa only [d1533, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1533, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13282 p hg
    simpa only [d1533, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13290 (p : Pattern) (guard : d4206 p = 1) : d1534 p ≤ (2 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1534, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12100 p hg
    simpa only [d1534, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1534, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12117 p hg
    simpa only [d1534, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13291 (p : Pattern) (guard : d4206 p = 1) : d1535 p ≤ (2 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1535, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13290 p hg
    simpa only [d1535, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1535, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12118 p hg
    simpa only [d1535, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13292 (p : Pattern) (guard : d4206 p = 1) : d1536 p ≤ (2 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1536, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12118 p hg
    simpa only [d1536, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1536, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1536, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13293 (p : Pattern) (guard : d4206 p = 1) : d1537 p ≤ (2 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1537, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13291 p hg
    simpa only [d1537, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1537, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13292 p hg
    simpa only [d1537, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13294 (p : Pattern) (guard : d4206 p = 1) : d1538 p ≤ (2 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13292 p hg
    simpa only [d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13295 (p : Pattern) (guard : d4206 p = 1) : d1539 p ≤ (2 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1539, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13293 p hg
    simpa only [d1539, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1539, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13294 p hg
    simpa only [d1539, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13296 (p : Pattern) (guard : d4206 p = 1) : d1540 p ≤ (2 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13294 p hg
    simpa only [d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13297 (p : Pattern) (guard : d4206 p = 1) : d1541 p ≤ (2 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1541, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13295 p hg
    simpa only [d1541, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1541, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13296 p hg
    simpa only [d1541, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13298 (p : Pattern) (guard : d4206 p = 1) : d1542 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1542, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13289 p hg
    simpa only [d1542, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1542, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13297 p hg
    simpa only [d1542, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13299 (p : Pattern) (guard : d4206 p = 1) : d1543 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1543, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13284 p hg
    simpa only [d1543, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1543, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13298 p hg
    simpa only [d1543, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
