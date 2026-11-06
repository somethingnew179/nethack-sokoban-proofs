/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions00
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s150 (pattern : Ten) : d228 (change pattern 0 10) = d228 pattern := by
  change (if pattern.g then d10 (change pattern 0 10) else d26 (change pattern 0 10)) = d228 pattern
  rw [s135, s140]
  rfl
theorem s151 (pattern : Ten) : d28 (change pattern 0 10) = d28 pattern := by
  change (if pattern.h then d10 (change pattern 0 10) else d22 (change pattern 0 10)) = d28 pattern
  rw [s135, s146]
  rfl
theorem s152 (pattern : Ten) : d229 (change pattern 0 10) = d229 pattern := by
  change (if pattern.g then d10 (change pattern 0 10) else d28 (change pattern 0 10)) = d229 pattern
  rw [s135, s151]
  rfl
theorem s153 (pattern : Ten) : d231 (change pattern 0 10) = d231 pattern := by
  change (if pattern.c then d229 (change pattern 0 10) else d228 (change pattern 0 10)) = d231 pattern
  rw [s152, s150]
  rfl
theorem s154 (pattern : Ten) : d232 (change pattern 0 10) = d410 pattern := by
  change (if pattern.e then d231 (change pattern 0 10) else d230 (change pattern 0 10)) = d410 pattern
  rw [s153, s149]
  rfl
theorem s155 (pattern : Ten) : d233 (change pattern 0 10) = d233 pattern := by
  change (if pattern.e then d10 (change pattern 0 10) else d231 (change pattern 0 10)) = d233 pattern
  rw [s135, s153]
  rfl
theorem s156 (pattern : Ten) : d234 (change pattern 0 10) = d411 pattern := by
  change (if pattern.d then d233 (change pattern 0 10) else d232 (change pattern 0 10)) = d411 pattern
  rw [s155, s154]
  rfl
theorem s157 (pattern : Ten) : d17 (change pattern 0 10) = d17 pattern := by
  change (if pattern.i then d12 (change pattern 0 10) else d0 (change pattern 0 10)) = d17 pattern
  rw [s136, s131]
  rfl
theorem s158 (pattern : Ten) : d23 (change pattern 0 10) = d23 pattern := by
  change (if pattern.h then d18 (change pattern 0 10) else d17 (change pattern 0 10)) = d23 pattern
  rw [s138, s157]
  rfl
theorem s159 (pattern : Ten) : d9 (change pattern 0 10) = d9 pattern := by
  rfl
theorem s160 (pattern : Ten) : d67 (change pattern 0 10) = d67 pattern := by
  change (if pattern.j then d9 (change pattern 0 10) else d0 (change pattern 0 10)) = d67 pattern
  rw [s159, s131]
  rfl
theorem s161 (pattern : Ten) : d68 (change pattern 0 10) = d68 pattern := by
  change (if pattern.j then d10 (change pattern 0 10) else d9 (change pattern 0 10)) = d68 pattern
  rw [s135, s159]
  rfl
theorem s162 (pattern : Ten) : d69 (change pattern 0 10) = d69 pattern := by
  change (if pattern.i then d68 (change pattern 0 10) else d67 (change pattern 0 10)) = d69 pattern
  rw [s161, s160]
  rfl
theorem s163 (pattern : Ten) : d70 (change pattern 0 10) = d70 pattern := by
  change (if pattern.i then d10 (change pattern 0 10) else d68 (change pattern 0 10)) = d70 pattern
  rw [s135, s161]
  rfl
theorem s164 (pattern : Ten) : d71 (change pattern 0 10) = d71 pattern := by
  change (if pattern.h then d70 (change pattern 0 10) else d69 (change pattern 0 10)) = d71 pattern
  rw [s163, s162]
  rfl
theorem s165 (pattern : Ten) : d73 (change pattern 0 10) = d73 pattern := by
  change (if pattern.g then d71 (change pattern 0 10) else d23 (change pattern 0 10)) = d73 pattern
  rw [s164, s158]
  rfl
theorem s166 (pattern : Ten) : d74 (change pattern 0 10) = d74 pattern := by
  change (if pattern.g then d71 (change pattern 0 10) else d25 (change pattern 0 10)) = d74 pattern
  rw [s164, s147]
  rfl
theorem s167 (pattern : Ten) : d77 (change pattern 0 10) = d77 pattern := by
  change (if pattern.c then d74 (change pattern 0 10) else d73 (change pattern 0 10)) = d77 pattern
  rw [s166, s165]
  rfl
theorem s168 (pattern : Ten) : d72 (change pattern 0 10) = d72 pattern := by
  change (if pattern.h then d10 (change pattern 0 10) else d70 (change pattern 0 10)) = d72 pattern
  rw [s135, s163]
  rfl
theorem s169 (pattern : Ten) : d75 (change pattern 0 10) = d75 pattern := by
  change (if pattern.g then d72 (change pattern 0 10) else d26 (change pattern 0 10)) = d75 pattern
  rw [s168, s140]
  rfl
theorem s170 (pattern : Ten) : d76 (change pattern 0 10) = d76 pattern := by
  change (if pattern.g then d72 (change pattern 0 10) else d28 (change pattern 0 10)) = d76 pattern
  rw [s168, s151]
  rfl
theorem s171 (pattern : Ten) : d78 (change pattern 0 10) = d78 pattern := by
  change (if pattern.c then d76 (change pattern 0 10) else d75 (change pattern 0 10)) = d78 pattern
  rw [s170, s169]
  rfl
theorem s172 (pattern : Ten) : d79 (change pattern 0 10) = d79 pattern := by
  change (if pattern.e then d78 (change pattern 0 10) else d77 (change pattern 0 10)) = d79 pattern
  rw [s171, s167]
  rfl
theorem s173 (pattern : Ten) : d80 (change pattern 0 10) = d80 pattern := by
  change (if pattern.e then d10 (change pattern 0 10) else d78 (change pattern 0 10)) = d80 pattern
  rw [s135, s171]
  rfl
theorem s174 (pattern : Ten) : d81 (change pattern 0 10) = d81 pattern := by
  change (if pattern.d then d80 (change pattern 0 10) else d79 (change pattern 0 10)) = d81 pattern
  rw [s173, s172]
  rfl
theorem s175 (pattern : Ten) : d0 (change pattern 0 1) = d0 pattern := by
  rfl
theorem s176 (pattern : Ten) : d10 (change pattern 0 1) = d10 pattern := by
  rfl
theorem s177 (pattern : Ten) : d12 (change pattern 0 1) = d12 pattern := by
  change (if pattern.j then d10 (change pattern 0 1) else d0 (change pattern 0 1)) = d12 pattern
  rw [s176, s175]
  rfl
theorem s178 (pattern : Ten) : d17 (change pattern 0 1) = d17 pattern := by
  change (if pattern.i then d12 (change pattern 0 1) else d0 (change pattern 0 1)) = d17 pattern
  rw [s177, s175]
  rfl
theorem s179 (pattern : Ten) : d18 (change pattern 0 1) = d18 pattern := by
  change (if pattern.i then d10 (change pattern 0 1) else d12 (change pattern 0 1)) = d18 pattern
  rw [s176, s177]
  rfl
theorem s180 (pattern : Ten) : d23 (change pattern 0 1) = d23 pattern := by
  change (if pattern.h then d18 (change pattern 0 1) else d17 (change pattern 0 1)) = d23 pattern
  rw [s179, s178]
  rfl
theorem s181 (pattern : Ten) : d9 (change pattern 0 1) = d9 pattern := by
  rfl
theorem s182 (pattern : Ten) : d67 (change pattern 0 1) = d67 pattern := by
  change (if pattern.j then d9 (change pattern 0 1) else d0 (change pattern 0 1)) = d67 pattern
  rw [s181, s175]
  rfl
theorem s183 (pattern : Ten) : d68 (change pattern 0 1) = d68 pattern := by
  change (if pattern.j then d10 (change pattern 0 1) else d9 (change pattern 0 1)) = d68 pattern
  rw [s176, s181]
  rfl
theorem s184 (pattern : Ten) : d69 (change pattern 0 1) = d69 pattern := by
  change (if pattern.i then d68 (change pattern 0 1) else d67 (change pattern 0 1)) = d69 pattern
  rw [s183, s182]
  rfl
theorem s185 (pattern : Ten) : d70 (change pattern 0 1) = d70 pattern := by
  change (if pattern.i then d10 (change pattern 0 1) else d68 (change pattern 0 1)) = d70 pattern
  rw [s176, s183]
  rfl
theorem s186 (pattern : Ten) : d71 (change pattern 0 1) = d71 pattern := by
  change (if pattern.h then d70 (change pattern 0 1) else d69 (change pattern 0 1)) = d71 pattern
  rw [s185, s184]
  rfl
theorem s187 (pattern : Ten) : d73 (change pattern 0 1) = d73 pattern := by
  change (if pattern.g then d71 (change pattern 0 1) else d23 (change pattern 0 1)) = d73 pattern
  rw [s186, s180]
  rfl
theorem s188 (pattern : Ten) : d2 (change pattern 0 1) = d2 pattern := by
  rfl
theorem s189 (pattern : Ten) : d15 (change pattern 0 1) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 0 1) else d0 (change pattern 0 1)) = d15 pattern
  rw [s188, s175]
  rfl
theorem s190 (pattern : Ten) : d16 (change pattern 0 1) = d16 pattern := by
  change (if pattern.j then d10 (change pattern 0 1) else d2 (change pattern 0 1)) = d16 pattern
  rw [s176, s188]
  rfl
theorem s191 (pattern : Ten) : d21 (change pattern 0 1) = d21 pattern := by
  change (if pattern.i then d16 (change pattern 0 1) else d15 (change pattern 0 1)) = d21 pattern
  rw [s190, s189]
  rfl
theorem s192 (pattern : Ten) : d22 (change pattern 0 1) = d22 pattern := by
  change (if pattern.i then d10 (change pattern 0 1) else d16 (change pattern 0 1)) = d22 pattern
  rw [s176, s190]
  rfl
theorem s193 (pattern : Ten) : d25 (change pattern 0 1) = d25 pattern := by
  change (if pattern.h then d22 (change pattern 0 1) else d21 (change pattern 0 1)) = d25 pattern
  rw [s192, s191]
  rfl
theorem s194 (pattern : Ten) : d74 (change pattern 0 1) = d74 pattern := by
  change (if pattern.g then d71 (change pattern 0 1) else d25 (change pattern 0 1)) = d74 pattern
  rw [s186, s193]
  rfl
theorem s195 (pattern : Ten) : d77 (change pattern 0 1) = d77 pattern := by
  change (if pattern.c then d74 (change pattern 0 1) else d73 (change pattern 0 1)) = d77 pattern
  rw [s194, s187]
  rfl
theorem s196 (pattern : Ten) : d26 (change pattern 0 1) = d26 pattern := by
  change (if pattern.h then d10 (change pattern 0 1) else d18 (change pattern 0 1)) = d26 pattern
  rw [s176, s179]
  rfl
theorem s197 (pattern : Ten) : d72 (change pattern 0 1) = d72 pattern := by
  change (if pattern.h then d10 (change pattern 0 1) else d70 (change pattern 0 1)) = d72 pattern
  rw [s176, s185]
  rfl
theorem s198 (pattern : Ten) : d75 (change pattern 0 1) = d75 pattern := by
  change (if pattern.g then d72 (change pattern 0 1) else d26 (change pattern 0 1)) = d75 pattern
  rw [s197, s196]
  rfl
theorem s199 (pattern : Ten) : d28 (change pattern 0 1) = d28 pattern := by
  change (if pattern.h then d10 (change pattern 0 1) else d22 (change pattern 0 1)) = d28 pattern
  rw [s176, s192]
  rfl
theorem s200 (pattern : Ten) : d76 (change pattern 0 1) = d76 pattern := by
  change (if pattern.g then d72 (change pattern 0 1) else d28 (change pattern 0 1)) = d76 pattern
  rw [s197, s199]
  rfl
theorem s201 (pattern : Ten) : d78 (change pattern 0 1) = d78 pattern := by
  change (if pattern.c then d76 (change pattern 0 1) else d75 (change pattern 0 1)) = d78 pattern
  rw [s200, s198]
  rfl
theorem s202 (pattern : Ten) : d79 (change pattern 0 1) = d79 pattern := by
  change (if pattern.e then d78 (change pattern 0 1) else d77 (change pattern 0 1)) = d79 pattern
  rw [s201, s195]
  rfl
theorem s203 (pattern : Ten) : d80 (change pattern 0 1) = d80 pattern := by
  change (if pattern.e then d10 (change pattern 0 1) else d78 (change pattern 0 1)) = d80 pattern
  rw [s176, s201]
  rfl
theorem s204 (pattern : Ten) : d81 (change pattern 0 1) = d81 pattern := by
  change (if pattern.d then d80 (change pattern 0 1) else d79 (change pattern 0 1)) = d81 pattern
  rw [s203, s202]
  rfl
theorem s205 (pattern : Ten) : d221 (change pattern 0 1) = d0 pattern := by
  change d0 (change pattern 0 1) = d0 pattern
  exact s175 pattern
theorem s206 (pattern : Ten) : d222 (change pattern 0 1) = d0 pattern := by
  change (if pattern.f then d0 (change pattern 0 1) else d221 (change pattern 0 1)) = d0 pattern
  rw [s175, s205]
  simp only [ite_self]
theorem s207 (pattern : Ten) : d223 (change pattern 0 1) = d0 pattern := by
  change (if pattern.j then d0 (change pattern 0 1) else d222 (change pattern 0 1)) = d0 pattern
  rw [s175, s206]
  simp only [ite_self]
theorem s208 (pattern : Ten) : d224 (change pattern 0 1) = d17 pattern := by
  change (if pattern.i then d12 (change pattern 0 1) else d223 (change pattern 0 1)) = d17 pattern
  rw [s177, s207]
  rfl
theorem s209 (pattern : Ten) : d225 (change pattern 0 1) = d23 pattern := by
  change (if pattern.h then d18 (change pattern 0 1) else d224 (change pattern 0 1)) = d23 pattern
  rw [s179, s208]
  rfl
theorem s210 (pattern : Ten) : d226 (change pattern 0 1) = d408 pattern := by
  change (if pattern.g then d26 (change pattern 0 1) else d225 (change pattern 0 1)) = d408 pattern
  rw [s196, s209]
  rfl
theorem s211 (pattern : Ten) : d227 (change pattern 0 1) = d227 pattern := by
  change (if pattern.g then d26 (change pattern 0 1) else d25 (change pattern 0 1)) = d227 pattern
  rw [s196, s193]
  rfl
theorem s212 (pattern : Ten) : d230 (change pattern 0 1) = d409 pattern := by
  change (if pattern.c then d227 (change pattern 0 1) else d226 (change pattern 0 1)) = d409 pattern
  rw [s211, s210]
  rfl
theorem s213 (pattern : Ten) : d228 (change pattern 0 1) = d228 pattern := by
  change (if pattern.g then d10 (change pattern 0 1) else d26 (change pattern 0 1)) = d228 pattern
  rw [s176, s196]
  rfl
theorem s214 (pattern : Ten) : d229 (change pattern 0 1) = d229 pattern := by
  change (if pattern.g then d10 (change pattern 0 1) else d28 (change pattern 0 1)) = d229 pattern
  rw [s176, s199]
  rfl
theorem s215 (pattern : Ten) : d231 (change pattern 0 1) = d231 pattern := by
  change (if pattern.c then d229 (change pattern 0 1) else d228 (change pattern 0 1)) = d231 pattern
  rw [s214, s213]
  rfl
theorem s216 (pattern : Ten) : d232 (change pattern 0 1) = d410 pattern := by
  change (if pattern.e then d231 (change pattern 0 1) else d230 (change pattern 0 1)) = d410 pattern
  rw [s215, s212]
  rfl
theorem s217 (pattern : Ten) : d233 (change pattern 0 1) = d233 pattern := by
  change (if pattern.e then d10 (change pattern 0 1) else d231 (change pattern 0 1)) = d233 pattern
  rw [s176, s215]
  rfl
theorem s218 (pattern : Ten) : d234 (change pattern 0 1) = d411 pattern := by
  change (if pattern.d then d233 (change pattern 0 1) else d232 (change pattern 0 1)) = d411 pattern
  rw [s217, s216]
  rfl
theorem s219 (pattern : Ten) : d12 (change pattern 10 10) = d12 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d0 (change pattern 10 10)) = d12 pattern
  rw [s4, s0]
  rfl
theorem s220 (pattern : Ten) : d17 (change pattern 10 10) = d17 pattern := by
  change (if pattern.i then d12 (change pattern 10 10) else d0 (change pattern 10 10)) = d17 pattern
  rw [s219, s0]
  rfl
theorem s221 (pattern : Ten) : d18 (change pattern 10 10) = d18 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d12 (change pattern 10 10)) = d18 pattern
  rw [s4, s219]
  rfl
theorem s222 (pattern : Ten) : d23 (change pattern 10 10) = d23 pattern := by
  change (if pattern.h then d18 (change pattern 10 10) else d17 (change pattern 10 10)) = d23 pattern
  rw [s221, s220]
  rfl
theorem s223 (pattern : Ten) : d13 (change pattern 10 10) = d13 pattern := by
  change (if pattern.j then d11 (change pattern 10 10) else d0 (change pattern 10 10)) = d13 pattern
  rw [s69, s0]
  rfl
theorem s224 (pattern : Ten) : d14 (change pattern 10 10) = d14 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d11 (change pattern 10 10)) = d14 pattern
  rw [s4, s69]
  rfl
theorem s225 (pattern : Ten) : d19 (change pattern 10 10) = d19 pattern := by
  change (if pattern.i then d14 (change pattern 10 10) else d13 (change pattern 10 10)) = d19 pattern
  rw [s224, s223]
  rfl
theorem s226 (pattern : Ten) : d20 (change pattern 10 10) = d20 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d14 (change pattern 10 10)) = d20 pattern
  rw [s4, s224]
  rfl
theorem s227 (pattern : Ten) : d24 (change pattern 10 10) = d24 pattern := by
  change (if pattern.h then d20 (change pattern 10 10) else d19 (change pattern 10 10)) = d24 pattern
  rw [s226, s225]
  rfl
theorem s228 (pattern : Ten) : d29 (change pattern 10 10) = d29 pattern := by
  change (if pattern.g then d24 (change pattern 10 10) else d23 (change pattern 10 10)) = d29 pattern
  rw [s227, s222]
  rfl
theorem s229 (pattern : Ten) : d16 (change pattern 10 10) = d16 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d2 (change pattern 10 10)) = d16 pattern
  rw [s4, s1]
  rfl
theorem s230 (pattern : Ten) : d21 (change pattern 10 10) = d21 pattern := by
  change (if pattern.i then d16 (change pattern 10 10) else d15 (change pattern 10 10)) = d21 pattern
  rw [s229, s2]
  rfl
theorem s231 (pattern : Ten) : d22 (change pattern 10 10) = d22 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d16 (change pattern 10 10)) = d22 pattern
  rw [s4, s229]
  rfl
theorem s232 (pattern : Ten) : d25 (change pattern 10 10) = d25 pattern := by
  change (if pattern.h then d22 (change pattern 10 10) else d21 (change pattern 10 10)) = d25 pattern
  rw [s231, s230]
  rfl
theorem s233 (pattern : Ten) : d30 (change pattern 10 10) = d30 pattern := by
  change (if pattern.g then d24 (change pattern 10 10) else d25 (change pattern 10 10)) = d30 pattern
  rw [s227, s232]
  rfl
theorem s234 (pattern : Ten) : d33 (change pattern 10 10) = d33 pattern := by
  change (if pattern.c then d30 (change pattern 10 10) else d29 (change pattern 10 10)) = d33 pattern
  rw [s233, s228]
  rfl
theorem s235 (pattern : Ten) : d26 (change pattern 10 10) = d26 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d18 (change pattern 10 10)) = d26 pattern
  rw [s4, s221]
  rfl
theorem s236 (pattern : Ten) : d27 (change pattern 10 10) = d27 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d20 (change pattern 10 10)) = d27 pattern
  rw [s4, s226]
  rfl
theorem s237 (pattern : Ten) : d31 (change pattern 10 10) = d31 pattern := by
  change (if pattern.g then d27 (change pattern 10 10) else d26 (change pattern 10 10)) = d31 pattern
  rw [s236, s235]
  rfl
theorem s238 (pattern : Ten) : d28 (change pattern 10 10) = d28 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d22 (change pattern 10 10)) = d28 pattern
  rw [s4, s231]
  rfl
theorem s239 (pattern : Ten) : d32 (change pattern 10 10) = d32 pattern := by
  change (if pattern.g then d27 (change pattern 10 10) else d28 (change pattern 10 10)) = d32 pattern
  rw [s236, s238]
  rfl
theorem s240 (pattern : Ten) : d34 (change pattern 10 10) = d34 pattern := by
  change (if pattern.c then d32 (change pattern 10 10) else d31 (change pattern 10 10)) = d34 pattern
  rw [s239, s237]
  rfl
theorem s241 (pattern : Ten) : d35 (change pattern 10 10) = d35 pattern := by
  change (if pattern.e then d34 (change pattern 10 10) else d33 (change pattern 10 10)) = d35 pattern
  rw [s240, s234]
  rfl
theorem s242 (pattern : Ten) : d36 (change pattern 10 10) = d36 pattern := by
  change (if pattern.e then d10 (change pattern 10 10) else d34 (change pattern 10 10)) = d36 pattern
  rw [s4, s240]
  rfl
theorem s243 (pattern : Ten) : d37 (change pattern 10 10) = d37 pattern := by
  change (if pattern.d then d36 (change pattern 10 10) else d35 (change pattern 10 10)) = d37 pattern
  rw [s242, s241]
  rfl
theorem s244 (pattern : Ten) : d0 (change pattern 10 0) = d0 pattern := by
  rfl
theorem s245 (pattern : Ten) : d10 (change pattern 10 0) = d10 pattern := by
  rfl
theorem s246 (pattern : Ten) : d12 (change pattern 10 0) = d12 pattern := by
  change (if pattern.j then d10 (change pattern 10 0) else d0 (change pattern 10 0)) = d12 pattern
  rw [s245, s244]
  rfl
theorem s247 (pattern : Ten) : d17 (change pattern 10 0) = d17 pattern := by
  change (if pattern.i then d12 (change pattern 10 0) else d0 (change pattern 10 0)) = d17 pattern
  rw [s246, s244]
  rfl
theorem s248 (pattern : Ten) : d18 (change pattern 10 0) = d18 pattern := by
  change (if pattern.i then d10 (change pattern 10 0) else d12 (change pattern 10 0)) = d18 pattern
  rw [s245, s246]
  rfl
theorem s249 (pattern : Ten) : d23 (change pattern 10 0) = d23 pattern := by
  change (if pattern.h then d18 (change pattern 10 0) else d17 (change pattern 10 0)) = d23 pattern
  rw [s248, s247]
  rfl
theorem s250 (pattern : Ten) : d11 (change pattern 10 0) = d10 pattern := by
  change d10 (change pattern 10 0) = d10 pattern
  exact s245 pattern
theorem s251 (pattern : Ten) : d13 (change pattern 10 0) = d12 pattern := by
  change (if pattern.j then d11 (change pattern 10 0) else d0 (change pattern 10 0)) = d12 pattern
  rw [s250, s244]
  rfl
theorem s252 (pattern : Ten) : d14 (change pattern 10 0) = d10 pattern := by
  change (if pattern.j then d10 (change pattern 10 0) else d11 (change pattern 10 0)) = d10 pattern
  rw [s245, s250]
  simp only [ite_self]
theorem s253 (pattern : Ten) : d19 (change pattern 10 0) = d18 pattern := by
  change (if pattern.i then d14 (change pattern 10 0) else d13 (change pattern 10 0)) = d18 pattern
  rw [s252, s251]
  rfl
theorem s254 (pattern : Ten) : d20 (change pattern 10 0) = d10 pattern := by
  change (if pattern.i then d10 (change pattern 10 0) else d14 (change pattern 10 0)) = d10 pattern
  rw [s245, s252]
  simp only [ite_self]
theorem s255 (pattern : Ten) : d24 (change pattern 10 0) = d26 pattern := by
  change (if pattern.h then d20 (change pattern 10 0) else d19 (change pattern 10 0)) = d26 pattern
  rw [s254, s253]
  rfl
theorem s256 (pattern : Ten) : d29 (change pattern 10 0) = d408 pattern := by
  change (if pattern.g then d24 (change pattern 10 0) else d23 (change pattern 10 0)) = d408 pattern
  rw [s255, s249]
  rfl
theorem s257 (pattern : Ten) : d2 (change pattern 10 0) = d2 pattern := by
  rfl
theorem s258 (pattern : Ten) : d15 (change pattern 10 0) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 10 0) else d0 (change pattern 10 0)) = d15 pattern
  rw [s257, s244]
  rfl
theorem s259 (pattern : Ten) : d16 (change pattern 10 0) = d16 pattern := by
  change (if pattern.j then d10 (change pattern 10 0) else d2 (change pattern 10 0)) = d16 pattern
  rw [s245, s257]
  rfl
theorem s260 (pattern : Ten) : d21 (change pattern 10 0) = d21 pattern := by
  change (if pattern.i then d16 (change pattern 10 0) else d15 (change pattern 10 0)) = d21 pattern
  rw [s259, s258]
  rfl
theorem s261 (pattern : Ten) : d22 (change pattern 10 0) = d22 pattern := by
  change (if pattern.i then d10 (change pattern 10 0) else d16 (change pattern 10 0)) = d22 pattern
  rw [s245, s259]
  rfl
theorem s262 (pattern : Ten) : d25 (change pattern 10 0) = d25 pattern := by
  change (if pattern.h then d22 (change pattern 10 0) else d21 (change pattern 10 0)) = d25 pattern
  rw [s261, s260]
  rfl
theorem s263 (pattern : Ten) : d30 (change pattern 10 0) = d227 pattern := by
  change (if pattern.g then d24 (change pattern 10 0) else d25 (change pattern 10 0)) = d227 pattern
  rw [s255, s262]
  rfl
theorem s264 (pattern : Ten) : d33 (change pattern 10 0) = d409 pattern := by
  change (if pattern.c then d30 (change pattern 10 0) else d29 (change pattern 10 0)) = d409 pattern
  rw [s263, s256]
  rfl
theorem s265 (pattern : Ten) : d26 (change pattern 10 0) = d26 pattern := by
  change (if pattern.h then d10 (change pattern 10 0) else d18 (change pattern 10 0)) = d26 pattern
  rw [s245, s248]
  rfl
theorem s266 (pattern : Ten) : d27 (change pattern 10 0) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 10 0) else d20 (change pattern 10 0)) = d10 pattern
  rw [s245, s254]
  simp only [ite_self]
theorem s267 (pattern : Ten) : d31 (change pattern 10 0) = d228 pattern := by
  change (if pattern.g then d27 (change pattern 10 0) else d26 (change pattern 10 0)) = d228 pattern
  rw [s266, s265]
  rfl
theorem s268 (pattern : Ten) : d28 (change pattern 10 0) = d28 pattern := by
  change (if pattern.h then d10 (change pattern 10 0) else d22 (change pattern 10 0)) = d28 pattern
  rw [s245, s261]
  rfl
theorem s269 (pattern : Ten) : d32 (change pattern 10 0) = d229 pattern := by
  change (if pattern.g then d27 (change pattern 10 0) else d28 (change pattern 10 0)) = d229 pattern
  rw [s266, s268]
  rfl
theorem s270 (pattern : Ten) : d34 (change pattern 10 0) = d231 pattern := by
  change (if pattern.c then d32 (change pattern 10 0) else d31 (change pattern 10 0)) = d231 pattern
  rw [s269, s267]
  rfl
theorem s271 (pattern : Ten) : d35 (change pattern 10 0) = d410 pattern := by
  change (if pattern.e then d34 (change pattern 10 0) else d33 (change pattern 10 0)) = d410 pattern
  rw [s270, s264]
  rfl
theorem s272 (pattern : Ten) : d36 (change pattern 10 0) = d233 pattern := by
  change (if pattern.e then d10 (change pattern 10 0) else d34 (change pattern 10 0)) = d233 pattern
  rw [s245, s270]
  rfl
theorem s273 (pattern : Ten) : d37 (change pattern 10 0) = d411 pattern := by
  change (if pattern.d then d36 (change pattern 10 0) else d35 (change pattern 10 0)) = d411 pattern
  rw [s272, s271]
  rfl
theorem s274 (pattern : Ten) : d1 (change pattern 10 0) = d1 pattern := by
  rfl
theorem s275 (pattern : Ten) : d171 (change pattern 10 0) = d1 pattern := by
  change d1 (change pattern 10 0) = d1 pattern
  exact s274 pattern
theorem s276 (pattern : Ten) : d173 (change pattern 10 0) = d412 pattern := by
  change (if pattern.j then d10 (change pattern 10 0) else d171 (change pattern 10 0)) = d412 pattern
  rw [s245, s275]
  rfl
theorem s277 (pattern : Ten) : d176 (change pattern 10 0) = d413 pattern := by
  change (if pattern.i then d173 (change pattern 10 0) else d171 (change pattern 10 0)) = d413 pattern
  rw [s276, s275]
  rfl
theorem s278 (pattern : Ten) : d177 (change pattern 10 0) = d414 pattern := by
  change (if pattern.i then d10 (change pattern 10 0) else d173 (change pattern 10 0)) = d414 pattern
  rw [s245, s276]
  rfl
theorem s279 (pattern : Ten) : d180 (change pattern 10 0) = d415 pattern := by
  change (if pattern.h then d177 (change pattern 10 0) else d176 (change pattern 10 0)) = d415 pattern
  rw [s278, s277]
  rfl
theorem s280 (pattern : Ten) : d181 (change pattern 10 0) = d416 pattern := by
  change (if pattern.h then d10 (change pattern 10 0) else d177 (change pattern 10 0)) = d416 pattern
  rw [s245, s278]
  rfl
theorem s281 (pattern : Ten) : d184 (change pattern 10 0) = d417 pattern := by
  change (if pattern.g then d181 (change pattern 10 0) else d180 (change pattern 10 0)) = d417 pattern
  rw [s280, s279]
  rfl
theorem s282 (pattern : Ten) : d3 (change pattern 10 0) = d3 pattern := by
  rfl
theorem s283 (pattern : Ten) : d172 (change pattern 10 0) = d3 pattern := by
  change d3 (change pattern 10 0) = d3 pattern
  exact s282 pattern
theorem s284 (pattern : Ten) : d174 (change pattern 10 0) = d418 pattern := by
  change (if pattern.j then d172 (change pattern 10 0) else d171 (change pattern 10 0)) = d418 pattern
  rw [s283, s275]
  rfl
theorem s285 (pattern : Ten) : d175 (change pattern 10 0) = d419 pattern := by
  change (if pattern.j then d10 (change pattern 10 0) else d172 (change pattern 10 0)) = d419 pattern
  rw [s245, s283]
  rfl
theorem s286 (pattern : Ten) : d178 (change pattern 10 0) = d420 pattern := by
  change (if pattern.i then d175 (change pattern 10 0) else d174 (change pattern 10 0)) = d420 pattern
  rw [s285, s284]
  rfl
theorem s287 (pattern : Ten) : d179 (change pattern 10 0) = d421 pattern := by
  change (if pattern.i then d10 (change pattern 10 0) else d175 (change pattern 10 0)) = d421 pattern
  rw [s245, s285]
  rfl
theorem s288 (pattern : Ten) : d182 (change pattern 10 0) = d422 pattern := by
  change (if pattern.h then d179 (change pattern 10 0) else d178 (change pattern 10 0)) = d422 pattern
  rw [s287, s286]
  rfl
theorem s289 (pattern : Ten) : d185 (change pattern 10 0) = d423 pattern := by
  change (if pattern.g then d181 (change pattern 10 0) else d182 (change pattern 10 0)) = d423 pattern
  rw [s280, s288]
  rfl
theorem s290 (pattern : Ten) : d188 (change pattern 10 0) = d424 pattern := by
  change (if pattern.c then d185 (change pattern 10 0) else d184 (change pattern 10 0)) = d424 pattern
  rw [s289, s281]
  rfl
theorem s291 (pattern : Ten) : d186 (change pattern 10 0) = d425 pattern := by
  change (if pattern.g then d10 (change pattern 10 0) else d181 (change pattern 10 0)) = d425 pattern
  rw [s245, s280]
  rfl
theorem s292 (pattern : Ten) : d183 (change pattern 10 0) = d426 pattern := by
  change (if pattern.h then d10 (change pattern 10 0) else d179 (change pattern 10 0)) = d426 pattern
  rw [s245, s287]
  rfl
theorem s293 (pattern : Ten) : d187 (change pattern 10 0) = d427 pattern := by
  change (if pattern.g then d10 (change pattern 10 0) else d183 (change pattern 10 0)) = d427 pattern
  rw [s245, s292]
  rfl
theorem s294 (pattern : Ten) : d189 (change pattern 10 0) = d428 pattern := by
  change (if pattern.c then d187 (change pattern 10 0) else d186 (change pattern 10 0)) = d428 pattern
  rw [s293, s291]
  rfl
theorem s295 (pattern : Ten) : d190 (change pattern 10 0) = d429 pattern := by
  change (if pattern.e then d189 (change pattern 10 0) else d188 (change pattern 10 0)) = d429 pattern
  rw [s294, s290]
  rfl
theorem s296 (pattern : Ten) : d191 (change pattern 10 0) = d430 pattern := by
  change (if pattern.e then d10 (change pattern 10 0) else d189 (change pattern 10 0)) = d430 pattern
  rw [s245, s294]
  rfl
theorem s297 (pattern : Ten) : d192 (change pattern 10 0) = d431 pattern := by
  change (if pattern.d then d191 (change pattern 10 0) else d190 (change pattern 10 0)) = d431 pattern
  rw [s296, s295]
  rfl
theorem s298 (pattern : Ten) : d7 (change pattern 10 3) = d7 pattern := by
  rfl
theorem s299 (pattern : Ten) : d8 (change pattern 10 3) = d8 pattern := by
  rfl
end NetHack.Sokoban41.Diagram
