/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6160 (p : Pattern) (guard : d8 p = 1) : d237 p ≤ (1 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6153 p hg
    simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6159 p hg
    simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6161 (p : Pattern) (guard : d8 p = 1) : d238 p ≤ (1 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6150 p hg
    simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6160 p hg
    simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6162 (p : Pattern) (guard : d8 p = 1) : d239 p ≤ (1 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6149 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6161 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6163 (p : Pattern) (guard : d8 p = 1) : d68 p ≤ (1 : Int) + d68 p := by
  omega
theorem compare6164 (p : Pattern) (guard : d8 p = 1) : d69 p ≤ (1 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6148 p hg
    simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6165 (p : Pattern) (guard : d8 p = 1) : d70 p ≤ (1 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6164 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6166 (p : Pattern) (guard : d8 p = 1) : d181 p ≤ (1 : Int) + d181 p := by
  omega
theorem compare6167 (p : Pattern) (guard : d8 p = 1) : d240 p ≤ (1 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6159 p hg
    simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6168 (p : Pattern) (guard : d8 p = 1) : d241 p ≤ (1 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6166 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6167 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6169 (p : Pattern) (guard : d8 p = 1) : d242 p ≤ (1 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6165 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6168 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6170 (p : Pattern) (guard : d8 p = 1) : d243 p ≤ (1 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6162 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6169 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6171 (p : Pattern) (guard : d8 p = 1) : d66 p ≤ (1 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6151 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6172 (p : Pattern) (guard : d8 p = 1) : d244 p ≤ (1 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6169 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6171 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6173 (p : Pattern) (guard : d8 p = 1) : d245 p ≤ (1 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6170 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6172 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6174 (p : Pattern) (guard : d8 p = 1) : d186 p ≤ (1 : Int) + d186 p := by
  omega
theorem compare6175 (p : Pattern) (guard : d8 p = 1) : d137 p ≤ (1 : Int) + d137 p := by
  omega
theorem compare6176 (p : Pattern) (guard : d8 p = 1) : d143 p ≤ (1 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d143, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6155 p hg
    simpa only [d143, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d143, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6145 p hg
    simpa only [d143, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6177 (p : Pattern) (guard : d8 p = 1) : d144 p ≤ (1 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6175 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6176 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6178 (p : Pattern) (guard : d8 p = 1) : d146 p ≤ (1 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6157 p hg
    simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6177 p hg
    simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6179 (p : Pattern) (guard : d8 p = 1) : d155 p ≤ (1 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6148 p hg
    simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6178 p hg
    simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6180 (p : Pattern) (guard : d8 p = 1) : d246 p ≤ (1 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6148 p hg
    simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6179 p hg
    simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6181 (p : Pattern) (guard : d8 p = 1) : d247 p ≤ (1 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6174 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6180 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6182 (p : Pattern) (guard : d8 p = 1) : d248 p ≤ (1 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6181 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6171 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6183 (p : Pattern) (guard : d8 p = 1) : d188 p ≤ (1 : Int) + d188 p := by
  omega
theorem compare6184 (p : Pattern) (guard : d8 p = 1) : d145 p ≤ (1 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6140 p hg
    simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6177 p hg
    simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6185 (p : Pattern) (guard : d8 p = 1) : d147 p ≤ (1 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6184 p hg
    simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6178 p hg
    simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6186 (p : Pattern) (guard : d8 p = 1) : d249 p ≤ (1 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6185 p hg
    simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6187 (p : Pattern) (guard : d8 p = 1) : d250 p ≤ (1 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6183 p hg
    simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6186 p hg
    simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6188 (p : Pattern) (guard : d8 p = 1) : d251 p ≤ (1 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6187 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6171 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6189 (p : Pattern) (guard : d8 p = 1) : d252 p ≤ (1 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6182 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6188 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6190 (p : Pattern) (guard : d8 p = 1) : d191 p ≤ (1 : Int) + d191 p := by
  omega
theorem compare6191 (p : Pattern) (guard : d8 p = 1) : d253 p ≤ (1 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6179 p hg
    simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6192 (p : Pattern) (guard : d8 p = 1) : d254 p ≤ (1 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6190 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6191 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6193 (p : Pattern) (guard : d8 p = 1) : d255 p ≤ (1 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6192 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6171 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6194 (p : Pattern) (guard : d8 p = 1) : d256 p ≤ (1 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6193 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6171 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6195 (p : Pattern) (guard : d8 p = 1) : d257 p ≤ (1 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6189 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6194 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6196 (p : Pattern) (guard : d8 p = 1) : d258 p ≤ (1 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6173 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6195 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6197 (p : Pattern) (guard : d1233 p = 1) : d35 p ≤ (0 : Int) + d0 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4952 p hg
    simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6198 (p : Pattern) (guard : d1233 p = 1) : d36 p ≤ (0 : Int) + d0 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5980 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6197 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6199 (p : Pattern) (guard : d1233 p = 1) : d16 p ≤ (0 : Int) + d0 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5278 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6200 (p : Pattern) (guard : d1233 p = 1) : d9 p ≤ (0 : Int) + d2 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4954 p hg
    simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6201 (p : Pattern) (guard : d1233 p = 1) : d37 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d37, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6199 p hg
    simpa only [d37, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d37, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6200 p hg
    simpa only [d37, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6202 (p : Pattern) (guard : d1233 p = 1) : d38 p ≤ (0 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d38, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6198 p hg
    simpa only [d38, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d38, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6201 p hg
    simpa only [d38, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6203 (p : Pattern) (guard : d1233 p = 1) : d39 p ≤ (0 : Int) + d0 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5980 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6199 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6204 (p : Pattern) (guard : d1233 p = 1) : d40 p ≤ (0 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d40, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6203 p hg
    simpa only [d40, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d40, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6201 p hg
    simpa only [d40, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6205 (p : Pattern) (guard : d1233 p = 1) : d41 p ≤ (0 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6202 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6204 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6206 (p : Pattern) (guard : d1233 p = 1) : d659 p ≤ (0 : Int) + d2 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d1233, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4961 p hg
    simpa only [d1233, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6207 (p : Pattern) (guard : d1233 p = 1) : d660 p ≤ (0 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5991 p hg
    simpa only [d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6206 p hg
    simpa only [d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6208 (p : Pattern) (guard : d1233 p = 1) : d262 p ≤ (0 : Int) + d2 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d1233, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5285 p hg
    simpa only [d1233, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6209 (p : Pattern) (guard : d1233 p = 1) : d58 p ≤ (0 : Int) + d4 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5996 p hg
    simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4963 p hg
    simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6210 (p : Pattern) (guard : d1233 p = 1) : d661 p ≤ (0 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d661, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6208 p hg
    simpa only [d661, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d661, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6209 p hg
    simpa only [d661, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6211 (p : Pattern) (guard : d1233 p = 1) : d662 p ≤ (0 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d662, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6207 p hg
    simpa only [d662, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d662, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6210 p hg
    simpa only [d662, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6212 (p : Pattern) (guard : d1233 p = 1) : d663 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d663, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6202 p hg
    simpa only [d663, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d663, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6211 p hg
    simpa only [d663, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6213 (p : Pattern) (guard : d1233 p = 1) : d664 p ≤ (0 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5991 p hg
    simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6208 p hg
    simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6214 (p : Pattern) (guard : d1233 p = 1) : d665 p ≤ (0 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d665, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6213 p hg
    simpa only [d665, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d665, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6210 p hg
    simpa only [d665, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6215 (p : Pattern) (guard : d1233 p = 1) : d666 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d666, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6204 p hg
    simpa only [d666, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d666, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6214 p hg
    simpa only [d666, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6216 (p : Pattern) (guard : d1233 p = 1) : d667 p ≤ (0 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6212 p hg
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6215 p hg
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6217 (p : Pattern) (guard : d1233 p = 1) : d668 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d668, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6205 p hg
    simpa only [d668, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d668, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6216 p hg
    simpa only [d668, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6218 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6219 (p : Pattern) (guard : d1233 p = 1) : d16 p ≤ (0 : Int) + d8 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d16, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1233, d16, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d16, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6218 p hg
    simpa only [d1233, d16, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6220 (p : Pattern) (guard : d1233 p = 1) : d37 p ≤ (0 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d37, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6219 p hg
    simpa only [d37, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d37, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6008 p hg
    simpa only [d37, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6221 (p : Pattern) (guard : d1233 p = 1) : d42 p ≤ (0 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d42, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6219 p hg
    simpa only [d42, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d42, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6220 p hg
    simpa only [d42, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6222 (p : Pattern) (guard : d1233 p = 1) : d43 p ≤ (0 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d43, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6204 p hg
    simpa only [d43, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d43, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6221 p hg
    simpa only [d43, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6223 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6224 (p : Pattern) (guard : d1233 p = 1) : d262 p ≤ (0 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d262, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d1233, d262, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d262, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6223 p hg
    simpa only [d1233, d262, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6225 (p : Pattern) (guard : d1233 p = 1) : d661 p ≤ (0 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d661, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6224 p hg
    simpa only [d661, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d661, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6014 p hg
    simpa only [d661, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6226 (p : Pattern) (guard : d1233 p = 1) : d669 p ≤ (0 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d669, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6224 p hg
    simpa only [d669, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d669, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6225 p hg
    simpa only [d669, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6227 (p : Pattern) (guard : d1233 p = 1) : d670 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d670, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6221 p hg
    simpa only [d670, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d670, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6226 p hg
    simpa only [d670, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6228 (p : Pattern) (guard : d1233 p = 1) : d671 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d671, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6215 p hg
    simpa only [d671, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d671, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6227 p hg
    simpa only [d671, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6229 (p : Pattern) (guard : d1233 p = 1) : d672 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d672, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6222 p hg
    simpa only [d672, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d672, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6228 p hg
    simpa only [d672, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6230 (p : Pattern) (guard : d1233 p = 1) : d673 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d673, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6217 p hg
    simpa only [d673, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d673, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6229 p hg
    simpa only [d673, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6231 (p : Pattern) (guard : d1233 p = 1) : d674 p ≤ (0 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6211 p hg
    simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6214 p hg
    simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6232 (p : Pattern) (guard : d1233 p = 1) : d675 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d675, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6205 p hg
    simpa only [d675, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d675, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d675, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6233 (p : Pattern) (guard : d1233 p = 1) : d676 p ≤ (0 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d676, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6202 p hg
    simpa only [d676, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d676, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6211 p hg
    simpa only [d676, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6234 (p : Pattern) (guard : d1233 p = 1) : d677 p ≤ (0 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d677, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6202 p hg
    simpa only [d677, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d677, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6233 p hg
    simpa only [d677, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6235 (p : Pattern) (guard : d1233 p = 1) : d678 p ≤ (0 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d678, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6204 p hg
    simpa only [d678, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d678, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6214 p hg
    simpa only [d678, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6236 (p : Pattern) (guard : d1233 p = 1) : d679 p ≤ (0 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d679, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6204 p hg
    simpa only [d679, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d679, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6235 p hg
    simpa only [d679, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6237 (p : Pattern) (guard : d1233 p = 1) : d680 p ≤ (0 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6234 p hg
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6236 p hg
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6238 (p : Pattern) (guard : d1233 p = 1) : d681 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d681, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6237 p hg
    simpa only [d681, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d681, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d681, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6239 (p : Pattern) (guard : d1233 p = 1) : d682 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d682, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6232 p hg
    simpa only [d682, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d682, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6238 p hg
    simpa only [d682, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6240 (p : Pattern) (guard : d1233 p = 1) : d683 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d683, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6232 p hg
    simpa only [d683, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d683, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6239 p hg
    simpa only [d683, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6241 (p : Pattern) (guard : d1233 p = 1) : d684 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d684, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6214 p hg
    simpa only [d684, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d684, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6226 p hg
    simpa only [d684, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6242 (p : Pattern) (guard : d1233 p = 1) : d685 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d685, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6222 p hg
    simpa only [d685, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d685, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d685, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6243 (p : Pattern) (guard : d1233 p = 1) : d686 p ≤ (0 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d686, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6221 p hg
    simpa only [d686, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d686, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6226 p hg
    simpa only [d686, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6244 (p : Pattern) (guard : d1233 p = 1) : d687 p ≤ (0 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d687, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6221 p hg
    simpa only [d687, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d687, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6243 p hg
    simpa only [d687, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6245 (p : Pattern) (guard : d1233 p = 1) : d688 p ≤ (0 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d688, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6236 p hg
    simpa only [d688, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d688, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6244 p hg
    simpa only [d688, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6246 (p : Pattern) (guard : d1233 p = 1) : d689 p ≤ (0 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d689, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6245 p hg
    simpa only [d689, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d689, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d689, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6247 (p : Pattern) (guard : d1233 p = 1) : d690 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d690, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6242 p hg
    simpa only [d690, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d690, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6246 p hg
    simpa only [d690, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6248 (p : Pattern) (guard : d1233 p = 1) : d691 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d691, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6242 p hg
    simpa only [d691, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d691, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d691, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6249 (p : Pattern) (guard : d1233 p = 1) : d692 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d692, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6240 p hg
    simpa only [d692, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d692, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6248 p hg
    simpa only [d692, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6250 (p : Pattern) (guard : d1233 p = 1) : d693 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d693, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6230 p hg
    simpa only [d693, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d693, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6249 p hg
    simpa only [d693, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6251 (p : Pattern) (guard : d1233 p = 1) : d694 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d694, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6217 p hg
    simpa only [d694, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d694, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d694, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6252 (p : Pattern) (guard : d1233 p = 1) : d695 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d695, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6229 p hg
    simpa only [d695, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d695, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d695, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6253 (p : Pattern) (guard : d1233 p = 1) : d696 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d696, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6251 p hg
    simpa only [d696, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d696, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6252 p hg
    simpa only [d696, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6254 (p : Pattern) (guard : d1233 p = 1) : d697 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d697, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6239 p hg
    simpa only [d697, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d697, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d697, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6255 (p : Pattern) (guard : d1233 p = 1) : d698 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d698, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d698, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d698, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d698, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6256 (p : Pattern) (guard : d1233 p = 1) : d699 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d699, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6254 p hg
    simpa only [d699, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d699, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6255 p hg
    simpa only [d699, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6257 (p : Pattern) (guard : d1233 p = 1) : d700 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d700, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6253 p hg
    simpa only [d700, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d700, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6256 p hg
    simpa only [d700, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6258 (p : Pattern) (guard : d1233 p = 1) : d701 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d701, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6250 p hg
    simpa only [d701, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d701, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6257 p hg
    simpa only [d701, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6259 (p : Pattern) (guard : d1233 p = 1) : d702 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d702, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d702, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d702, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d702, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6260 (p : Pattern) (guard : d1233 p = 1) : d703 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d703, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6257 p hg
    simpa only [d703, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d703, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d703, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6261 (p : Pattern) (guard : d1233 p = 1) : d704 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d704, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6258 p hg
    simpa only [d704, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d704, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6260 p hg
    simpa only [d704, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6262 (p : Pattern) (guard : d1233 p = 1) : d705 p ≤ (0 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d705, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6233 p hg
    simpa only [d705, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d705, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6211 p hg
    simpa only [d705, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6263 (p : Pattern) (guard : d1233 p = 1) : d706 p ≤ (0 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d706, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6235 p hg
    simpa only [d706, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d706, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6214 p hg
    simpa only [d706, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6264 (p : Pattern) (guard : d1233 p = 1) : d707 p ≤ (0 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6262 p hg
    simpa only [d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6263 p hg
    simpa only [d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6265 (p : Pattern) (guard : d1233 p = 1) : d708 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d708, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6237 p hg
    simpa only [d708, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d708, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6264 p hg
    simpa only [d708, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6266 (p : Pattern) (guard : d1233 p = 1) : d709 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d709, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6217 p hg
    simpa only [d709, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d709, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6265 p hg
    simpa only [d709, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6267 (p : Pattern) (guard : d1233 p = 1) : d710 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d710, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6217 p hg
    simpa only [d710, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d710, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6266 p hg
    simpa only [d710, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6268 (p : Pattern) (guard : d1233 p = 1) : d711 p ≤ (0 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d711, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6243 p hg
    simpa only [d711, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d711, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6226 p hg
    simpa only [d711, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6269 (p : Pattern) (guard : d1233 p = 1) : d712 p ≤ (0 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d712, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6263 p hg
    simpa only [d712, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d712, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6268 p hg
    simpa only [d712, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6270 (p : Pattern) (guard : d1233 p = 1) : d713 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d713, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6245 p hg
    simpa only [d713, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d713, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6269 p hg
    simpa only [d713, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6271 (p : Pattern) (guard : d1233 p = 1) : d714 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d714, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6229 p hg
    simpa only [d714, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d714, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d714, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6272 (p : Pattern) (guard : d1233 p = 1) : d715 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d715, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6229 p hg
    simpa only [d715, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d715, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6271 p hg
    simpa only [d715, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6273 (p : Pattern) (guard : d1233 p = 1) : d716 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d716, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6267 p hg
    simpa only [d716, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d716, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6272 p hg
    simpa only [d716, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6274 (p : Pattern) (guard : d1233 p = 1) : d717 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d717, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6273 p hg
    simpa only [d717, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d717, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d717, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6275 (p : Pattern) (guard : d1233 p = 1) : d718 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d718, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6205 p hg
    simpa only [d718, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d718, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6264 p hg
    simpa only [d718, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6276 (p : Pattern) (guard : d1233 p = 1) : d719 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d719, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6275 p hg
    simpa only [d719, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d719, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6265 p hg
    simpa only [d719, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6277 (p : Pattern) (guard : d1233 p = 1) : d720 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d720, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6276 p hg
    simpa only [d720, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d720, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d720, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6278 (p : Pattern) (guard : d1233 p = 1) : d721 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d721, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6222 p hg
    simpa only [d721, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d721, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6269 p hg
    simpa only [d721, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6279 (p : Pattern) (guard : d1233 p = 1) : d722 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d722, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6278 p hg
    simpa only [d722, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d722, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d722, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6280 (p : Pattern) (guard : d1233 p = 1) : d723 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d723, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6279 p hg
    simpa only [d723, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d723, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d723, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6281 (p : Pattern) (guard : d1233 p = 1) : d724 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d724, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6277 p hg
    simpa only [d724, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d724, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6280 p hg
    simpa only [d724, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6282 (p : Pattern) (guard : d1233 p = 1) : d725 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d725, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6281 p hg
    simpa only [d725, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d725, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d725, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6283 (p : Pattern) (guard : d1233 p = 1) : d726 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d726, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6274 p hg
    simpa only [d726, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d726, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6282 p hg
    simpa only [d726, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6284 (p : Pattern) (guard : d1233 p = 1) : d727 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d727, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6266 p hg
    simpa only [d727, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d727, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d727, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6285 (p : Pattern) (guard : d1233 p = 1) : d728 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d728, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6271 p hg
    simpa only [d728, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d728, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d728, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6286 (p : Pattern) (guard : d1233 p = 1) : d729 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d729, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6284 p hg
    simpa only [d729, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d729, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6285 p hg
    simpa only [d729, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6287 (p : Pattern) (guard : d1233 p = 1) : d730 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d730, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6286 p hg
    simpa only [d730, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d730, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d730, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6288 (p : Pattern) (guard : d1233 p = 1) : d731 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d731, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6287 p hg
    simpa only [d731, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d731, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d731, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6289 (p : Pattern) (guard : d1233 p = 1) : d732 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d732, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6283 p hg
    simpa only [d732, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d732, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6288 p hg
    simpa only [d732, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6290 (p : Pattern) (guard : d1233 p = 1) : d733 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d733, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6261 p hg
    simpa only [d733, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d733, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6289 p hg
    simpa only [d733, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6291 (p : Pattern) (guard : d1233 p = 1) : d258 p ≤ (0 : Int) + d258 p := by
  omega
theorem compare6292 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (3 : Int) + d258 p := by
  omega
theorem compare6293 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) ≤ (0 : Int) + 3
  decide
theorem compare6294 (p : Pattern) (guard : d1233 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6295 (p : Pattern) (guard : d1309 p = 1) : d0 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d1309, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d1309, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6296 (p : Pattern) (guard : d1310 p = 1) : d0 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1310, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d1310, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1309 p = 1 := by simpa only [d1310, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6295 p hg
    simpa only [d1310, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6297 (p : Pattern) (guard : d1312 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6298 (p : Pattern) (guard : d1313 p = 1) : d0 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1310 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6296 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1312 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6297 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6299 (p : Pattern) (guard : d1315 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
end NetHack.Sokoban12CostPartition
