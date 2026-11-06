/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions117
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub14160 (p : Pattern) : d3198 (change p 10000 (some 247)) = d8054 p := by
  change (if p 161 then d3059 (change p 10000 (some 247)) else d3197 (change p 10000 (some 247))) = d8054 p
  rw [sub14001, sub14159]
  rfl
theorem sub14161 (p : Pattern) : d3199 (change p 10000 (some 247)) = d8055 p := by
  change (if p 160 then d3063 (change p 10000 (some 247)) else d3198 (change p 10000 (some 247))) = d8055 p
  rw [sub14005, sub14160]
  rfl
theorem sub14162 (p : Pattern) : d2154 (change p 10000 (some 247)) = d11 p := by
  change d11 (change p 10000 (some 247)) = d11 p
  exact sub13697 p
theorem sub14163 (p : Pattern) : d2155 (change p 10000 (some 247)) = d3257 p := by
  change (if p 246 then d39 (change p 10000 (some 247)) else d2154 (change p 10000 (some 247))) = d3257 p
  rw [sub13699, sub14162]
  rfl
theorem sub14164 (p : Pattern) : d2156 (change p 10000 (some 247)) = d8056 p := by
  change (if p 225 then d2155 (change p 10000 (some 247)) else d1895 (change p 10000 (some 247))) = d8056 p
  rw [sub14163, sub13909]
  rfl
theorem sub14165 (p : Pattern) : d2157 (change p 10000 (some 247)) = d8057 p := by
  change (if p 224 then d2156 (change p 10000 (some 247)) else d1893 (change p 10000 (some 247))) = d8057 p
  rw [sub14164, sub13907]
  rfl
theorem sub14166 (p : Pattern) : d2158 (change p 10000 (some 247)) = d8058 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2157 (change p 10000 (some 247))) = d8058 p
  rw [sub13654, sub14165]
  rfl
theorem sub14167 (p : Pattern) : d3200 (change p 10000 (some 247)) = d8059 p := by
  change (if p 182 then d2158 (change p 10000 (some 247)) else d3023 (change p 10000 (some 247))) = d8059 p
  rw [sub14166, sub13955]
  rfl
theorem sub14168 (p : Pattern) : d3201 (change p 10000 (some 247)) = d8060 p := by
  change (if p 163 then d3048 (change p 10000 (some 247)) else d3200 (change p 10000 (some 247))) = d8060 p
  rw [sub13990, sub14167]
  rfl
theorem sub14169 (p : Pattern) : d3202 (change p 10000 (some 247)) = d8061 p := by
  change (if p 162 then d3151 (change p 10000 (some 247)) else d3201 (change p 10000 (some 247))) = d8061 p
  rw [sub14107, sub14168]
  rfl
theorem sub14170 (p : Pattern) : d3203 (change p 10000 (some 247)) = d8062 p := by
  change (if p 161 then d3062 (change p 10000 (some 247)) else d3202 (change p 10000 (some 247))) = d8062 p
  rw [sub14004, sub14169]
  rfl
theorem sub14171 (p : Pattern) : d3204 (change p 10000 (some 247)) = d8063 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d2958 (change p 10000 (some 247))) = d8063 p
  rw [sub13654, sub13825]
  rfl
theorem sub14172 (p : Pattern) : d3205 (change p 10000 (some 247)) = d8064 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d3204 (change p 10000 (some 247))) = d8064 p
  rw [sub13654, sub14171]
  rfl
theorem sub14173 (p : Pattern) : d3206 (change p 10000 (some 247)) = d8065 p := by
  change (if p 160 then d3205 (change p 10000 (some 247)) else d3203 (change p 10000 (some 247))) = d8065 p
  rw [sub14172, sub14170]
  rfl
theorem sub14174 (p : Pattern) : d3207 (change p 10000 (some 247)) = d8066 p := by
  change (if p 141 then d3206 (change p 10000 (some 247)) else d3199 (change p 10000 (some 247))) = d8066 p
  rw [sub14173, sub14161]
  rfl
theorem sub14175 (p : Pattern) : d3208 (change p 10000 (some 247)) = d8067 p := by
  change (if p 138 then d3207 (change p 10000 (some 247)) else d3194 (change p 10000 (some 247))) = d8067 p
  rw [sub14174, sub14156]
  rfl
theorem sub14176 (p : Pattern) : d3209 (change p 10000 (some 247)) = d8068 p := by
  change (if p 163 then d2957 (change p 10000 (some 247)) else d3048 (change p 10000 (some 247))) = d8068 p
  rw [sub13824, sub13990]
  rfl
theorem sub14177 (p : Pattern) : d3210 (change p 10000 (some 247)) = d8069 p := by
  change (if p 162 then d3209 (change p 10000 (some 247)) else d3195 (change p 10000 (some 247))) = d8069 p
  rw [sub14176, sub14157]
  rfl
theorem sub14178 (p : Pattern) : d3211 (change p 10000 (some 247)) = d8070 p := by
  change (if p 163 then d2957 (change p 10000 (some 247)) else d3043 (change p 10000 (some 247))) = d8070 p
  rw [sub13824, sub13985]
  rfl
theorem sub14179 (p : Pattern) : d3212 (change p 10000 (some 247)) = d8071 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3211 (change p 10000 (some 247))) = d8071 p
  rw [sub13654, sub14178]
  rfl
theorem sub14180 (p : Pattern) : d3213 (change p 10000 (some 247)) = d8072 p := by
  change (if p 161 then d3212 (change p 10000 (some 247)) else d3210 (change p 10000 (some 247))) = d8072 p
  rw [sub14179, sub14177]
  rfl
theorem sub14181 (p : Pattern) : d3214 (change p 10000 (some 247)) = d8073 p := by
  change (if p 163 then d2931 (change p 10000 (some 247)) else d3050 (change p 10000 (some 247))) = d8073 p
  rw [sub13783, sub13992]
  rfl
theorem sub14182 (p : Pattern) : d3215 (change p 10000 (some 247)) = d8074 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3214 (change p 10000 (some 247))) = d8074 p
  rw [sub13654, sub14181]
  rfl
theorem sub14183 (p : Pattern) : d3216 (change p 10000 (some 247)) = d8075 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d3215 (change p 10000 (some 247))) = d8075 p
  rw [sub13654, sub14182]
  rfl
theorem sub14184 (p : Pattern) : d3217 (change p 10000 (some 247)) = d8076 p := by
  change (if p 160 then d3216 (change p 10000 (some 247)) else d3213 (change p 10000 (some 247))) = d8076 p
  rw [sub14183, sub14180]
  rfl
theorem sub14185 (p : Pattern) : d3218 (change p 10000 (some 247)) = d8077 p := by
  change (if p 141 then d3206 (change p 10000 (some 247)) else d3217 (change p 10000 (some 247))) = d8077 p
  rw [sub14173, sub14184]
  rfl
theorem sub14186 (p : Pattern) : d3219 (change p 10000 (some 247)) = d8078 p := by
  change (if p 138 then d12 (change p 10000 (some 247)) else d3218 (change p 10000 (some 247))) = d8078 p
  rw [sub13654, sub14185]
  rfl
theorem sub14187 (p : Pattern) : d3220 (change p 10000 (some 247)) = d8079 p := by
  change (if p 116 then d3219 (change p 10000 (some 247)) else d3208 (change p 10000 (some 247))) = d8079 p
  rw [sub14186, sub14175]
  rfl
theorem sub14188 (p : Pattern) : d3221 (change p 10000 (some 247)) = d8080 p := by
  change (if p 115 then d3220 (change p 10000 (some 247)) else d3159 (change p 10000 (some 247))) = d8080 p
  rw [sub14187, sub14115]
  rfl
theorem sub14189 (p : Pattern) : d3222 (change p 10000 (some 247)) = d8081 p := by
  change (if p 71 then d3221 (change p 10000 (some 247)) else d2992 (change p 10000 (some 247))) = d8081 p
  rw [sub14188, sub13859]
  rfl
theorem sub14190 (p : Pattern) : d3223 (change p 10000 (some 247)) = d8082 p := by
  change (if p 49 then d3222 (change p 10000 (some 247)) else d3140 (change p 10000 (some 247))) = d8082 p
  rw [sub14189, sub14096]
  rfl
theorem sub14191 (p : Pattern) : d3224 (change p 10000 (some 247)) = d8083 p := by
  change (if p 48 then d3223 (change p 10000 (some 247)) else d3077 (change p 10000 (some 247))) = d8083 p
  rw [sub14190, sub14019]
  rfl
end NetHack.Sokoban22Refined85
