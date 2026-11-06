/- Untrusted proposed candidate; every stated lemma uses the Lean kernel. -/
import NetHack.Soko22Hazard87.Nodes119
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def bonus (hero : Cell) (p : Pattern) : Int :=
  if hero = 25 then d2518 p else
  if hero = 27 then d2671 p else
  if hero = 28 then d2671 p else
  if hero = 29 then d2671 p else
  if hero = 30 then d2671 p else
  if hero = 45 then d2518 p else
  if hero = 46 then d2518 p else
  if hero = 47 then d2518 p else
  if hero = 48 then d2782 p else
  if hero = 49 then d2895 p else
  if hero = 50 then d3015 p else
  if hero = 51 then d3142 p else
  if hero = 52 then d2671 p else
  if hero = 67 then d2518 p else
  if hero = 69 then d3318 p else
  if hero = 70 then d3496 p else
  if hero = 71 then d3673 p else
  if hero = 73 then d3842 p else
  if hero = 74 then d4025 p else
  if hero = 89 then d4334 p else
  if hero = 90 then d4650 p else
  if hero = 91 then d5349 p else
  if hero = 111 then d5849 p else
  if hero = 113 then d6737 p else
  if hero = 114 then d7239 p else
  if hero = 133 then d5849 p else
  if hero = 134 then d5849 p else
  if hero = 135 then d8234 p else
  if hero = 136 then d9291 p else
  if hero = 141 then d10648 p else
  if hero = 155 then d5849 p else
  if hero = 156 then d5849 p else
  if hero = 157 then d12224 p else
  if hero = 158 then d13979 p else
  if hero = 159 then d15965 p else
  if hero = 160 then d17560 p else
  if hero = 161 then d18533 p else
  if hero = 162 then d19737 p else
  if hero = 163 then d20389 p else
  if hero = 164 then d20891 p else
  if hero = 177 then d5849 p else
  if hero = 180 then d23134 p else
  if hero = 181 then d17560 p else
  if hero = 182 then d17560 p else
  if hero = 184 then d20891 p else
  if hero = 185 then d20891 p else
  if hero = 186 then d20891 p else
  if hero = 199 then d5849 p else
  if hero = 200 then d5849 p else
  if hero = 201 then d25101 p else
  if hero = 202 then d27480 p else
  if hero = 204 then d28738 p else
  if hero = 223 then d30634 p else
  if hero = 224 then d33212 p else
  if hero = 225 then d36004 p else
  if hero = 226 then d38812 p else
  if hero = 245 then d40148 p else
  if hero = 246 then d42245 p else
  if hero = 247 then d44879 p else
  if hero = 248 then d47282 p else
  if hero = 249 then d47282 p else
  if hero = 250 then d47326 p else
  if hero = 251 then d47371 p else
  if hero = 252 then d47417 p else
  if hero = 253 then d47464 p else
  if hero = 254 then d47512 p else
  if hero = 255 then d47561 p else
  if hero = 256 then d47611 p else
  0
theorem at25 (p : Pattern) : bonus 25 p = d2518 p := by rfl
theorem at27 (p : Pattern) : bonus 27 p = d2671 p := by rfl
theorem at28 (p : Pattern) : bonus 28 p = d2671 p := by rfl
theorem at29 (p : Pattern) : bonus 29 p = d2671 p := by rfl
theorem at30 (p : Pattern) : bonus 30 p = d2671 p := by rfl
theorem at45 (p : Pattern) : bonus 45 p = d2518 p := by rfl
theorem at46 (p : Pattern) : bonus 46 p = d2518 p := by rfl
theorem at47 (p : Pattern) : bonus 47 p = d2518 p := by rfl
theorem at48 (p : Pattern) : bonus 48 p = d2782 p := by rfl
theorem at49 (p : Pattern) : bonus 49 p = d2895 p := by rfl
theorem at50 (p : Pattern) : bonus 50 p = d3015 p := by rfl
theorem at51 (p : Pattern) : bonus 51 p = d3142 p := by rfl
theorem at52 (p : Pattern) : bonus 52 p = d2671 p := by rfl
theorem at67 (p : Pattern) : bonus 67 p = d2518 p := by rfl
theorem at69 (p : Pattern) : bonus 69 p = d3318 p := by rfl
theorem at70 (p : Pattern) : bonus 70 p = d3496 p := by rfl
theorem at71 (p : Pattern) : bonus 71 p = d3673 p := by rfl
theorem at73 (p : Pattern) : bonus 73 p = d3842 p := by rfl
theorem at74 (p : Pattern) : bonus 74 p = d4025 p := by rfl
theorem at76 (p : Pattern) : bonus 76 p = d0 p := by rfl
theorem at78 (p : Pattern) : bonus 78 p = d0 p := by rfl
theorem at79 (p : Pattern) : bonus 79 p = d0 p := by rfl
theorem at80 (p : Pattern) : bonus 80 p = d0 p := by rfl
theorem at81 (p : Pattern) : bonus 81 p = d0 p := by rfl
theorem at82 (p : Pattern) : bonus 82 p = d0 p := by rfl
theorem at83 (p : Pattern) : bonus 83 p = d0 p := by rfl
theorem at84 (p : Pattern) : bonus 84 p = d0 p := by rfl
theorem at89 (p : Pattern) : bonus 89 p = d4334 p := by rfl
theorem at90 (p : Pattern) : bonus 90 p = d4650 p := by rfl
theorem at91 (p : Pattern) : bonus 91 p = d5349 p := by rfl
theorem at93 (p : Pattern) : bonus 93 p = d0 p := by rfl
theorem at94 (p : Pattern) : bonus 94 p = d0 p := by rfl
theorem at95 (p : Pattern) : bonus 95 p = d0 p := by rfl
theorem at96 (p : Pattern) : bonus 96 p = d0 p := by rfl
theorem at97 (p : Pattern) : bonus 97 p = d0 p := by rfl
theorem at98 (p : Pattern) : bonus 98 p = d0 p := by rfl
theorem at100 (p : Pattern) : bonus 100 p = d0 p := by rfl
theorem at101 (p : Pattern) : bonus 101 p = d0 p := by rfl
theorem at102 (p : Pattern) : bonus 102 p = d0 p := by rfl
theorem at103 (p : Pattern) : bonus 103 p = d0 p := by rfl
theorem at104 (p : Pattern) : bonus 104 p = d0 p := by rfl
theorem at105 (p : Pattern) : bonus 105 p = d0 p := by rfl
theorem at106 (p : Pattern) : bonus 106 p = d0 p := by rfl
theorem at111 (p : Pattern) : bonus 111 p = d5849 p := by rfl
theorem at113 (p : Pattern) : bonus 113 p = d6737 p := by rfl
theorem at114 (p : Pattern) : bonus 114 p = d7239 p := by rfl
theorem at115 (p : Pattern) : bonus 115 p = d0 p := by rfl
theorem at116 (p : Pattern) : bonus 116 p = d0 p := by rfl
theorem at118 (p : Pattern) : bonus 118 p = d0 p := by rfl
theorem at119 (p : Pattern) : bonus 119 p = d0 p := by rfl
theorem at120 (p : Pattern) : bonus 120 p = d0 p := by rfl
theorem at122 (p : Pattern) : bonus 122 p = d0 p := by rfl
theorem at123 (p : Pattern) : bonus 123 p = d0 p := by rfl
theorem at124 (p : Pattern) : bonus 124 p = d0 p := by rfl
theorem at125 (p : Pattern) : bonus 125 p = d0 p := by rfl
theorem at126 (p : Pattern) : bonus 126 p = d0 p := by rfl
theorem at127 (p : Pattern) : bonus 127 p = d0 p := by rfl
theorem at128 (p : Pattern) : bonus 128 p = d0 p := by rfl
theorem at133 (p : Pattern) : bonus 133 p = d5849 p := by rfl
theorem at134 (p : Pattern) : bonus 134 p = d5849 p := by rfl
theorem at135 (p : Pattern) : bonus 135 p = d8234 p := by rfl
theorem at136 (p : Pattern) : bonus 136 p = d9291 p := by rfl
theorem at138 (p : Pattern) : bonus 138 p = d0 p := by rfl
theorem at141 (p : Pattern) : bonus 141 p = d10648 p := by rfl
theorem at144 (p : Pattern) : bonus 144 p = d0 p := by rfl
theorem at145 (p : Pattern) : bonus 145 p = d0 p := by rfl
theorem at146 (p : Pattern) : bonus 146 p = d0 p := by rfl
theorem at147 (p : Pattern) : bonus 147 p = d0 p := by rfl
theorem at148 (p : Pattern) : bonus 148 p = d0 p := by rfl
theorem at149 (p : Pattern) : bonus 149 p = d0 p := by rfl
theorem at150 (p : Pattern) : bonus 150 p = d0 p := by rfl
theorem at155 (p : Pattern) : bonus 155 p = d5849 p := by rfl
theorem at156 (p : Pattern) : bonus 156 p = d5849 p := by rfl
theorem at157 (p : Pattern) : bonus 157 p = d12224 p := by rfl
theorem at158 (p : Pattern) : bonus 158 p = d13979 p := by rfl
theorem at159 (p : Pattern) : bonus 159 p = d15965 p := by rfl
theorem at160 (p : Pattern) : bonus 160 p = d17560 p := by rfl
theorem at161 (p : Pattern) : bonus 161 p = d18533 p := by rfl
theorem at162 (p : Pattern) : bonus 162 p = d19737 p := by rfl
theorem at163 (p : Pattern) : bonus 163 p = d20389 p := by rfl
theorem at164 (p : Pattern) : bonus 164 p = d20891 p := by rfl
theorem at166 (p : Pattern) : bonus 166 p = d0 p := by rfl
theorem at167 (p : Pattern) : bonus 167 p = d0 p := by rfl
theorem at168 (p : Pattern) : bonus 168 p = d0 p := by rfl
theorem at169 (p : Pattern) : bonus 169 p = d0 p := by rfl
theorem at170 (p : Pattern) : bonus 170 p = d0 p := by rfl
theorem at171 (p : Pattern) : bonus 171 p = d0 p := by rfl
theorem at172 (p : Pattern) : bonus 172 p = d0 p := by rfl
theorem at177 (p : Pattern) : bonus 177 p = d5849 p := by rfl
theorem at180 (p : Pattern) : bonus 180 p = d23134 p := by rfl
theorem at181 (p : Pattern) : bonus 181 p = d17560 p := by rfl
theorem at182 (p : Pattern) : bonus 182 p = d17560 p := by rfl
theorem at184 (p : Pattern) : bonus 184 p = d20891 p := by rfl
theorem at185 (p : Pattern) : bonus 185 p = d20891 p := by rfl
theorem at186 (p : Pattern) : bonus 186 p = d20891 p := by rfl
theorem at188 (p : Pattern) : bonus 188 p = d0 p := by rfl
theorem at189 (p : Pattern) : bonus 189 p = d0 p := by rfl
theorem at190 (p : Pattern) : bonus 190 p = d0 p := by rfl
theorem at191 (p : Pattern) : bonus 191 p = d0 p := by rfl
theorem at192 (p : Pattern) : bonus 192 p = d0 p := by rfl
theorem at193 (p : Pattern) : bonus 193 p = d0 p := by rfl
theorem at194 (p : Pattern) : bonus 194 p = d0 p := by rfl
theorem at199 (p : Pattern) : bonus 199 p = d5849 p := by rfl
theorem at200 (p : Pattern) : bonus 200 p = d5849 p := by rfl
theorem at201 (p : Pattern) : bonus 201 p = d25101 p := by rfl
theorem at202 (p : Pattern) : bonus 202 p = d27480 p := by rfl
theorem at204 (p : Pattern) : bonus 204 p = d28738 p := by rfl
theorem at210 (p : Pattern) : bonus 210 p = d0 p := by rfl
theorem at211 (p : Pattern) : bonus 211 p = d0 p := by rfl
theorem at212 (p : Pattern) : bonus 212 p = d0 p := by rfl
theorem at213 (p : Pattern) : bonus 213 p = d0 p := by rfl
theorem at214 (p : Pattern) : bonus 214 p = d0 p := by rfl
theorem at215 (p : Pattern) : bonus 215 p = d0 p := by rfl
theorem at216 (p : Pattern) : bonus 216 p = d0 p := by rfl
theorem at218 (p : Pattern) : bonus 218 p = d0 p := by rfl
theorem at223 (p : Pattern) : bonus 223 p = d30634 p := by rfl
theorem at224 (p : Pattern) : bonus 224 p = d33212 p := by rfl
theorem at225 (p : Pattern) : bonus 225 p = d36004 p := by rfl
theorem at226 (p : Pattern) : bonus 226 p = d38812 p := by rfl
theorem at240 (p : Pattern) : bonus 240 p = d0 p := by rfl
theorem at245 (p : Pattern) : bonus 245 p = d40148 p := by rfl
theorem at246 (p : Pattern) : bonus 246 p = d42245 p := by rfl
theorem at247 (p : Pattern) : bonus 247 p = d44879 p := by rfl
theorem at248 (p : Pattern) : bonus 248 p = d47282 p := by rfl
theorem at249 (p : Pattern) : bonus 249 p = d47282 p := by rfl
theorem at250 (p : Pattern) : bonus 250 p = d47326 p := by rfl
theorem at251 (p : Pattern) : bonus 251 p = d47371 p := by rfl
theorem at252 (p : Pattern) : bonus 252 p = d47417 p := by rfl
theorem at253 (p : Pattern) : bonus 253 p = d47464 p := by rfl
theorem at254 (p : Pattern) : bonus 254 p = d47512 p := by rfl
theorem at255 (p : Pattern) : bonus 255 p = d47561 p := by rfl
theorem at256 (p : Pattern) : bonus 256 p = d47611 p := by rfl
theorem at257 (p : Pattern) : bonus 257 p = d0 p := by rfl
theorem at258 (p : Pattern) : bonus 258 p = d0 p := by rfl
theorem at259 (p : Pattern) : bonus 259 p = d0 p := by rfl
theorem at260 (p : Pattern) : bonus 260 p = d0 p := by rfl
theorem at262 (p : Pattern) : bonus 262 p = d0 p := by rfl
theorem bonus_range (hero : Cell) (p : Pattern) : 0 ≤ bonus hero p ∧ bonus hero p ≤ 2 := by
  unfold bonus
  simpa only [decide_eq_true_eq, d0] using range_ite (decide (hero = 25)) (d2518 p) _ (range2518 p) (range_ite (decide (hero = 27)) (d2671 p) _ (range2671 p) (range_ite (decide (hero = 28)) (d2671 p) _ (range2671 p) (range_ite (decide (hero = 29)) (d2671 p) _ (range2671 p) (range_ite (decide (hero = 30)) (d2671 p) _ (range2671 p) (range_ite (decide (hero = 45)) (d2518 p) _ (range2518 p) (range_ite (decide (hero = 46)) (d2518 p) _ (range2518 p) (range_ite (decide (hero = 47)) (d2518 p) _ (range2518 p) (range_ite (decide (hero = 48)) (d2782 p) _ (range2782 p) (range_ite (decide (hero = 49)) (d2895 p) _ (range2895 p) (range_ite (decide (hero = 50)) (d3015 p) _ (range3015 p) (range_ite (decide (hero = 51)) (d3142 p) _ (range3142 p) (range_ite (decide (hero = 52)) (d2671 p) _ (range2671 p) (range_ite (decide (hero = 67)) (d2518 p) _ (range2518 p) (range_ite (decide (hero = 69)) (d3318 p) _ (range3318 p) (range_ite (decide (hero = 70)) (d3496 p) _ (range3496 p) (range_ite (decide (hero = 71)) (d3673 p) _ (range3673 p) (range_ite (decide (hero = 73)) (d3842 p) _ (range3842 p) (range_ite (decide (hero = 74)) (d4025 p) _ (range4025 p) (range_ite (decide (hero = 89)) (d4334 p) _ (range4334 p) (range_ite (decide (hero = 90)) (d4650 p) _ (range4650 p) (range_ite (decide (hero = 91)) (d5349 p) _ (range5349 p) (range_ite (decide (hero = 111)) (d5849 p) _ (range5849 p) (range_ite (decide (hero = 113)) (d6737 p) _ (range6737 p) (range_ite (decide (hero = 114)) (d7239 p) _ (range7239 p) (range_ite (decide (hero = 133)) (d5849 p) _ (range5849 p) (range_ite (decide (hero = 134)) (d5849 p) _ (range5849 p) (range_ite (decide (hero = 135)) (d8234 p) _ (range8234 p) (range_ite (decide (hero = 136)) (d9291 p) _ (range9291 p) (range_ite (decide (hero = 141)) (d10648 p) _ (range10648 p) (range_ite (decide (hero = 155)) (d5849 p) _ (range5849 p) (range_ite (decide (hero = 156)) (d5849 p) _ (range5849 p) (range_ite (decide (hero = 157)) (d12224 p) _ (range12224 p) (range_ite (decide (hero = 158)) (d13979 p) _ (range13979 p) (range_ite (decide (hero = 159)) (d15965 p) _ (range15965 p) (range_ite (decide (hero = 160)) (d17560 p) _ (range17560 p) (range_ite (decide (hero = 161)) (d18533 p) _ (range18533 p) (range_ite (decide (hero = 162)) (d19737 p) _ (range19737 p) (range_ite (decide (hero = 163)) (d20389 p) _ (range20389 p) (range_ite (decide (hero = 164)) (d20891 p) _ (range20891 p) (range_ite (decide (hero = 177)) (d5849 p) _ (range5849 p) (range_ite (decide (hero = 180)) (d23134 p) _ (range23134 p) (range_ite (decide (hero = 181)) (d17560 p) _ (range17560 p) (range_ite (decide (hero = 182)) (d17560 p) _ (range17560 p) (range_ite (decide (hero = 184)) (d20891 p) _ (range20891 p) (range_ite (decide (hero = 185)) (d20891 p) _ (range20891 p) (range_ite (decide (hero = 186)) (d20891 p) _ (range20891 p) (range_ite (decide (hero = 199)) (d5849 p) _ (range5849 p) (range_ite (decide (hero = 200)) (d5849 p) _ (range5849 p) (range_ite (decide (hero = 201)) (d25101 p) _ (range25101 p) (range_ite (decide (hero = 202)) (d27480 p) _ (range27480 p) (range_ite (decide (hero = 204)) (d28738 p) _ (range28738 p) (range_ite (decide (hero = 223)) (d30634 p) _ (range30634 p) (range_ite (decide (hero = 224)) (d33212 p) _ (range33212 p) (range_ite (decide (hero = 225)) (d36004 p) _ (range36004 p) (range_ite (decide (hero = 226)) (d38812 p) _ (range38812 p) (range_ite (decide (hero = 245)) (d40148 p) _ (range40148 p) (range_ite (decide (hero = 246)) (d42245 p) _ (range42245 p) (range_ite (decide (hero = 247)) (d44879 p) _ (range44879 p) (range_ite (decide (hero = 248)) (d47282 p) _ (range47282 p) (range_ite (decide (hero = 249)) (d47282 p) _ (range47282 p) (range_ite (decide (hero = 250)) (d47326 p) _ (range47326 p) (range_ite (decide (hero = 251)) (d47371 p) _ (range47371 p) (range_ite (decide (hero = 252)) (d47417 p) _ (range47417 p) (range_ite (decide (hero = 253)) (d47464 p) _ (range47464 p) (range_ite (decide (hero = 254)) (d47512 p) _ (range47512 p) (range_ite (decide (hero = 255)) (d47561 p) _ (range47561 p) (range_ite (decide (hero = 256)) (d47611 p) _ (range47611 p) (range0 p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem goal0 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d0 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal2518 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d2518 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d2518, d2517, d2516, d2515, d2514, d2513, d2512, d2511, d2510, d2509, d2508, d2507, d2506, d2505, d2504, d2503, d2502, d2501, d2500, d2499, d2498, d2497, d2496, d2495, d2494, d2493, d2492, d2491, d2490, d2489, d2488, d2487, d2486, d2485, d2484, d2483, d2482, d2481, d2480, d2479, d2478, d2477, d2476, d2475, d1996, d1518, d1083, d749, d474, d279, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal2671 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d2671 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d2671, d2670, d2669, d2668, d2667, d2666, d2665, d2664, d2663, d2662, d2661, d2660, d2659, d2658, d2657, d2656, d2655, d2654, d2653, d2652, d2651, d2650, d2649, d2648, d2647, d2646, d2645, d2644, d2643, d2642, d2641, d2640, d2639, d2638, d2637, d2636, d2635, d2634, d2633, d2632, d2631, d2630, d2629, d2628, d2610, d2593, d2577, d2562, d2548, d2535, d2524, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal2782 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d2782 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d2782, d2781, d2780, d2779, d2778, d2777, d2776, d2775, d2774, d2773, d2772, d2771, d2770, d2769, d2768, d2767, d2766, d2765, d2764, d2763, d2762, d2761, d2760, d2759, d2758, d2757, d2756, d2755, d2754, d2753, d2752, d2751, d2750, d2749, d2748, d2747, d2746, d2745, d2744, d2743, d2742, d2741, d2740, d2739, d2727, d2716, d2706, d2697, d2689, d2682, d2676, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal2895 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d2895 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d2895, d2894, d2893, d2892, d2891, d2890, d2889, d2888, d2887, d2886, d2885, d2884, d2883, d2882, d2881, d2880, d2879, d2878, d2877, d2876, d2875, d2874, d2873, d2872, d2871, d2870, d2869, d2868, d2867, d2866, d2865, d2864, d2863, d2862, d2861, d2860, d2859, d2858, d2857, d2856, d2855, d2854, d2853, d2852, d2839, d2827, d2816, d2806, d2797, d2789, d2524, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal3015 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d3015 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d3015, d3014, d3013, d3012, d3011, d3010, d3009, d3008, d3007, d3006, d3005, d3004, d3003, d3002, d3001, d3000, d2999, d2998, d2997, d2996, d2995, d2994, d2993, d2992, d2991, d2990, d2989, d2988, d2987, d2986, d2985, d2984, d2983, d2982, d2981, d2980, d2979, d2978, d2977, d2976, d2975, d2974, d2973, d2972, d2958, d2945, d2933, d2922, d2912, d2903, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal3142 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d3142 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d3142, d3141, d3140, d3139, d3138, d3137, d3136, d3135, d3134, d3133, d3132, d3131, d3130, d3129, d3128, d3127, d3126, d3125, d3124, d3123, d3122, d3121, d3120, d3119, d3118, d3117, d3116, d3115, d3114, d3113, d3112, d3111, d3110, d3109, d3108, d3107, d3106, d3105, d3104, d3103, d3102, d3101, d3100, d3099, d3084, d3070, d3057, d3045, d3034, d3024, d2524, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal3318 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d3318 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d3318, d3317, d3316, d3315, d3314, d3313, d3312, d3311, d3310, d3309, d3308, d3307, d3306, d3305, d3304, d3303, d3302, d3301, d3300, d3299, d3298, d3297, d3296, d3295, d3294, d3293, d3292, d3291, d3290, d3289, d3288, d3287, d3286, d3285, d3284, d3283, d3282, d3281, d3280, d3279, d3278, d3277, d3276, d3275, d3252, d3230, d3209, d3189, d3170, d3152, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal3496 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d3496 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d3496, d3495, d3494, d3493, d3492, d3491, d3490, d3489, d3488, d3487, d3486, d3485, d3484, d3483, d3482, d3481, d3480, d3479, d3478, d3477, d3476, d3475, d3474, d3473, d3472, d3471, d3470, d3469, d3468, d3467, d3466, d3465, d3464, d3463, d3462, d3461, d3460, d3459, d3458, d3457, d3456, d3455, d3454, d3453, d3432, d3412, d3393, d3375, d3358, d3342, d3328, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal3673 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d3673 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d3673, d3672, d3671, d3670, d3669, d3668, d3667, d3666, d3665, d3664, d3663, d3662, d3661, d3660, d3659, d3658, d3657, d3656, d3655, d3654, d3653, d3652, d3651, d3650, d3649, d3648, d3647, d3646, d3645, d3644, d3643, d3642, d3641, d3640, d3639, d3638, d3637, d3636, d3635, d3634, d3633, d3632, d3631, d3630, d3609, d3589, d3570, d3552, d3535, d3520, d3507, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal3842 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d3842 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d3842, d3841, d3840, d3839, d3838, d3837, d3836, d3835, d3834, d3833, d3832, d3831, d3830, d3829, d3828, d3827, d3826, d3825, d3824, d3823, d3822, d3821, d3820, d3819, d3818, d3817, d3816, d3815, d3814, d3813, d3812, d3811, d3810, d3809, d3808, d3807, d3806, d3805, d3804, d3803, d3802, d3801, d3800, d3799, d3778, d3758, d3739, d3721, d3704, d3688, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal4025 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d4025 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d4025, d4024, d4023, d4022, d4021, d4020, d4019, d4018, d4017, d4016, d4015, d4014, d4013, d4012, d4011, d4010, d4009, d4008, d4007, d4006, d4005, d4004, d4003, d4002, d4001, d4000, d3999, d3998, d3997, d3996, d3995, d3994, d3993, d3992, d3991, d3990, d3989, d3988, d3987, d3986, d3985, d3984, d3983, d3982, d3959, d3937, d3916, d3896, d3877, d3859, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal4334 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d4334 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d4334, d4333, d4332, d4331, d4330, d4329, d4328, d4327, d4326, d4325, d4324, d4323, d4322, d4321, d4320, d4319, d4318, d4317, d4316, d4315, d4314, d4313, d4312, d4311, d4310, d4309, d4308, d4307, d4306, d4305, d4304, d4303, d4302, d4301, d4300, d4299, d4298, d4297, d4296, d4295, d4294, d4293, d4292, d4291, d4250, d4210, d4171, d4133, d4096, d4060, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal4650 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d4650 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d4650, d4649, d4648, d4647, d4646, d4645, d4644, d4643, d4642, d4641, d4640, d4639, d4638, d4637, d4636, d4635, d4634, d4633, d4632, d4631, d4630, d4629, d4628, d4627, d4626, d4625, d4624, d4623, d4622, d4621, d4620, d4619, d4618, d4617, d4616, d4615, d4614, d4613, d4612, d4611, d4610, d4609, d4608, d4607, d4565, d4524, d4484, d4445, d4407, d4370, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal5349 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d5349 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d5349, d5348, d5347, d5346, d5345, d5344, d5343, d5342, d5341, d5340, d5339, d5338, d5337, d5336, d5335, d5334, d5333, d5332, d5331, d5330, d5329, d5328, d5327, d5326, d5325, d5324, d5323, d5322, d5321, d5320, d5319, d5318, d5317, d5316, d5315, d5314, d5313, d5312, d5311, d5310, d5309, d5308, d5307, d5306, d5192, d5075, d4964, d4868, d4773, d4688, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal5849 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d5849 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d5849, d5848, d5847, d5846, d5845, d5844, d5843, d5842, d5841, d5840, d5839, d5838, d5837, d5836, d5835, d5834, d5833, d5832, d5831, d5830, d5829, d5828, d5827, d5826, d5825, d5824, d5823, d5822, d5821, d5820, d5819, d5818, d5817, d5816, d5815, d5814, d5813, d5812, d5811, d5810, d5809, d5808, d5807, d5806, d5714, d5623, d5533, d5447, d5395, d279, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal6737 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d6737 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d6737, d6736, d6735, d6734, d6733, d6732, d6731, d6730, d6729, d6728, d6727, d6726, d6725, d6724, d6723, d6722, d6721, d6720, d6719, d6718, d6717, d6716, d6715, d6714, d6713, d6712, d6711, d6710, d6709, d6708, d6707, d6706, d6705, d6704, d6703, d6702, d6701, d6700, d6699, d6698, d6697, d6696, d6695, d6694, d6546, d6399, d6253, d6114, d5991, d5890, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal7239 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d7239 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d7239, d7238, d7237, d7236, d7235, d7234, d7233, d7232, d7231, d7230, d7229, d7228, d7227, d7226, d7225, d7224, d7223, d7222, d7221, d7220, d7219, d7218, d7217, d7216, d7215, d7214, d7213, d7212, d7211, d7210, d7209, d7208, d7207, d7206, d7205, d7204, d7203, d7202, d7201, d7200, d7199, d7198, d7197, d7196, d7114, d7033, d6953, d6874, d6796, d279, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal8234 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d8234 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d8234, d8233, d8232, d8231, d8230, d8229, d8228, d8227, d8226, d8225, d8224, d8223, d8222, d8221, d8220, d8219, d8218, d8217, d8216, d8215, d8214, d8213, d8212, d8211, d8210, d8209, d8208, d8207, d8206, d8205, d8204, d8203, d8202, d8201, d8200, d8199, d8198, d8197, d8196, d8195, d8194, d8193, d8192, d8191, d8035, d7880, d7726, d7573, d7429, d7297, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal9291 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d9291 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d9291, d9290, d9289, d9288, d9287, d9286, d9285, d9284, d9283, d9282, d9281, d9280, d9279, d9278, d9277, d9276, d9275, d9274, d9273, d9272, d9271, d9270, d9269, d9268, d9267, d9266, d9265, d9264, d9263, d9262, d9261, d9260, d9259, d9258, d9257, d9256, d9255, d9254, d9253, d9252, d9251, d9250, d9249, d9248, d9078, d8909, d8741, d8574, d8416, d8284, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal10648 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d10648 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d10648, d10647, d10646, d10645, d10644, d10643, d10642, d10641, d10640, d10639, d10638, d10637, d10636, d10635, d10634, d10633, d10632, d10631, d10630, d10629, d10628, d10627, d10626, d10625, d10624, d10623, d10622, d10621, d10620, d10619, d10618, d10617, d10616, d10615, d10614, d10613, d10612, d10611, d10610, d10609, d10608, d10607, d10606, d10605, d10338, d10031, d9745, d9575, d9448, d9376, d9324, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal12224 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d12224 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d12224, d12223, d12222, d12221, d12220, d12219, d12218, d12217, d12216, d12215, d12214, d12213, d12212, d12211, d12210, d12209, d12208, d12207, d12206, d12205, d12204, d12203, d12202, d12201, d12200, d12199, d12198, d12197, d12196, d12195, d12194, d12193, d12192, d12191, d12190, d12189, d12188, d12187, d12186, d12185, d12184, d12183, d12182, d12181, d11908, d11636, d11365, d11095, d10862, d10714, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal13979 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d13979 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d13979, d13978, d13977, d13976, d13975, d13974, d13973, d13972, d13971, d13970, d13969, d13968, d13967, d13966, d13965, d13964, d13963, d13962, d13961, d13960, d13959, d13958, d13957, d13956, d13955, d13954, d13953, d13952, d13951, d13950, d13949, d13948, d13947, d13946, d13945, d13944, d13943, d13942, d13941, d13940, d13939, d13938, d13937, d13936, d13608, d13281, d12955, d12687, d12436, d12284, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal15965 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d15965 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d15965, d15964, d15963, d15962, d15961, d15960, d15959, d15958, d15957, d15956, d15955, d15954, d15953, d15952, d15951, d15950, d15949, d15948, d15947, d15946, d15945, d15944, d15943, d15942, d15941, d15940, d15939, d15938, d15937, d15936, d15935, d15934, d15933, d15932, d15931, d15930, d15929, d15928, d15927, d15926, d15925, d15924, d15923, d15922, d15543, d15149, d14756, d14466, d14207, d14049, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal17560 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d17560 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d17560, d17559, d17558, d17557, d17556, d17555, d17554, d17553, d17552, d17551, d17550, d17549, d17548, d17547, d17546, d17545, d17544, d17543, d17542, d17541, d17540, d17539, d17538, d17537, d17536, d17535, d17534, d17533, d17532, d17531, d17530, d17529, d17528, d17527, d17526, d17525, d17524, d17523, d17522, d17521, d17520, d17519, d17518, d17517, d17152, d16786, d16437, d16226, d16034, d279, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal18533 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d18533 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d18533, d18532, d18531, d18530, d18529, d18528, d18527, d18526, d18525, d18524, d18523, d18522, d18521, d18520, d18519, d18518, d18517, d18516, d18515, d18514, d18513, d18512, d18511, d18510, d18509, d18508, d18507, d18506, d18505, d18504, d18503, d18502, d18501, d18500, d18499, d18498, d18497, d18496, d18495, d18494, d18493, d18492, d18491, d18490, d18308, d18122, d17941, d17811, d17708, d17642, d17592, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal19737 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d19737 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d19737, d19736, d19735, d19734, d19733, d19732, d19731, d19730, d19729, d19728, d19727, d19726, d19725, d19724, d19723, d19722, d19721, d19720, d19719, d19718, d19717, d19716, d19715, d19714, d19713, d19712, d19711, d19710, d19709, d19708, d19707, d19706, d19705, d19704, d19703, d19702, d19701, d19700, d19699, d19698, d19697, d19696, d19695, d19694, d19461, d19222, d18990, d18830, d18707, d18630, d18570, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal20389 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d20389 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d20389, d20388, d20387, d20386, d20385, d20384, d20383, d20382, d20381, d20380, d20379, d20378, d20377, d20376, d20375, d20374, d20373, d20372, d20371, d20370, d20369, d20368, d20367, d20366, d20365, d20364, d20363, d20362, d20361, d20360, d20359, d20358, d20357, d20356, d20355, d20354, d20353, d20352, d20351, d20350, d20349, d20348, d20347, d20346, d20240, d20135, d20031, d19940, d19857, d19804, d19764, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal20891 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d20891 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d20891, d20890, d20889, d20888, d20887, d20886, d20885, d20884, d20883, d20882, d20881, d20880, d20879, d20878, d20877, d20876, d20875, d20874, d20873, d20872, d20871, d20870, d20869, d20868, d20867, d20866, d20865, d20864, d20863, d20862, d20861, d20860, d20859, d20858, d20857, d20856, d20855, d20854, d20853, d20852, d20851, d20850, d20849, d20848, d20773, d20699, d20626, d20557, d20489, d20444, d20412, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal23134 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d23134 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d23134, d23133, d23132, d23131, d23130, d23129, d23128, d23127, d23126, d23125, d23124, d23123, d23122, d23121, d23120, d23119, d23118, d23117, d23116, d23115, d23114, d23113, d23112, d23111, d23110, d23109, d23108, d23107, d23106, d23105, d23104, d23103, d23102, d23101, d23100, d23099, d23098, d23097, d23096, d23095, d23094, d23093, d23092, d23091, d22684, d22218, d21735, d21417, d21128, d20961, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal25101 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d25101 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d25101, d25100, d25099, d25098, d25097, d25096, d25095, d25094, d25093, d25092, d25091, d25090, d25089, d25088, d25087, d25086, d25085, d25084, d25083, d25082, d25081, d25080, d25079, d25078, d25077, d25076, d25075, d25074, d25073, d25072, d25071, d25070, d25069, d25068, d25067, d25066, d25065, d25064, d25063, d25062, d25061, d25060, d25059, d25058, d24689, d24306, d23926, d23628, d23365, d23200, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal27480 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d27480 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d27480, d27479, d27478, d27477, d27476, d27475, d27474, d27473, d27472, d27471, d27470, d27469, d27468, d27467, d27466, d27465, d27464, d27463, d27462, d27461, d27460, d27459, d27458, d27457, d27456, d27455, d27454, d27453, d27452, d27451, d27450, d27449, d27448, d27447, d27446, d27445, d27444, d27443, d27442, d27441, d27440, d27439, d27438, d27437, d27013, d26549, d26078, d25689, d25374, d25182, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal28738 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d28738 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d28738, d28737, d28736, d28735, d28734, d28733, d28732, d28731, d28730, d28729, d28728, d28727, d28726, d28725, d28724, d28723, d28722, d28721, d28720, d28719, d28718, d28717, d28716, d28715, d28714, d28713, d28712, d28711, d28710, d28709, d28708, d28707, d28706, d28705, d28704, d28703, d28702, d28701, d28700, d28699, d28698, d28697, d28696, d28695, d28094, d16786, d16437, d16226, d16034, d279, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal30634 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d30634 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d30634, d30633, d30632, d30631, d30630, d30629, d30628, d30627, d30626, d30625, d30624, d30623, d30622, d30621, d30620, d30619, d30618, d30617, d30616, d30615, d30614, d30613, d30612, d30611, d30610, d30609, d30608, d30607, d30606, d30605, d30604, d30603, d30602, d30601, d30600, d30599, d30598, d30597, d30596, d30595, d30594, d30593, d30592, d30591, d30076, d29526, d29087, d28834, d16034, d279, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal33212 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d33212 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d33212, d33211, d33210, d33209, d33208, d33207, d33206, d33205, d33204, d33203, d33202, d33201, d33200, d33199, d33198, d33197, d33196, d33195, d33194, d33193, d33192, d33191, d33190, d33189, d33188, d33187, d33186, d33185, d33184, d33183, d33182, d33181, d33180, d33179, d33178, d33177, d33176, d33175, d33174, d33173, d33172, d33171, d33170, d33169, d32686, d32139, d31620, d31230, d30912, d30716, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal36004 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d36004 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d36004, d36003, d36002, d36001, d36000, d35999, d35998, d35997, d35996, d35995, d35994, d35993, d35992, d35991, d35990, d35989, d35988, d35987, d35986, d35985, d35984, d35983, d35982, d35981, d35980, d35979, d35978, d35977, d35976, d35975, d35974, d35973, d35972, d35971, d35970, d35969, d35968, d35967, d35966, d35965, d35964, d35963, d35962, d35961, d35361, d34781, d34224, d33821, d33499, d33298, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal38812 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d38812 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d38812, d38811, d38810, d38809, d38808, d38807, d38806, d38805, d38804, d38803, d38802, d38801, d38800, d38799, d38798, d38797, d38796, d38795, d38794, d38793, d38792, d38791, d38790, d38789, d38788, d38787, d38786, d38785, d38784, d38783, d38782, d38781, d38780, d38779, d38778, d38777, d38776, d38775, d38774, d38773, d38772, d38771, d38770, d38769, d38154, d37494, d36977, d36593, d36279, d36085, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal40148 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d40148 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d40148, d40147, d40146, d40145, d40144, d40143, d40142, d40141, d40140, d40139, d40138, d40137, d40136, d40135, d40134, d40133, d40132, d40131, d40130, d40129, d40128, d40127, d40126, d40125, d40124, d40123, d40122, d40121, d40120, d40119, d40118, d40117, d40116, d40115, d40114, d40113, d40112, d40111, d40110, d40109, d40108, d40107, d40106, d40105, d39703, d39243, d29087, d28834, d16034, d279, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal42245 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d42245 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d42245, d42244, d42243, d42242, d42241, d42240, d42239, d42238, d42237, d42236, d42235, d42234, d42233, d42232, d42231, d42230, d42229, d42228, d42227, d42226, d42225, d42224, d42223, d42222, d42221, d42220, d42219, d42218, d42217, d42216, d42215, d42214, d42213, d42212, d42211, d42210, d42209, d42208, d42207, d42206, d42205, d42204, d42203, d42202, d42201, d41655, d41155, d40758, d40437, d40235, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal44879 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d44879 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d44879, d44878, d44877, d44876, d44875, d44874, d44873, d44872, d44871, d44870, d44869, d44868, d44867, d44866, d44865, d44864, d44863, d44862, d44861, d44860, d44859, d44858, d44857, d44856, d44855, d44854, d44853, d44852, d44851, d44850, d44849, d44848, d44847, d44846, d44845, d44844, d44843, d44842, d44841, d44840, d44839, d44838, d44837, d44836, d44440, d43842, d43277, d42863, d42537, d42333, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal47282 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d47282 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d47282, d47281, d47280, d47279, d47278, d47277, d47276, d47275, d47274, d47273, d47272, d47271, d47270, d47269, d47268, d47267, d47266, d47265, d47264, d47263, d47262, d47261, d47260, d47259, d47258, d47257, d47256, d47255, d47254, d47253, d47252, d47251, d47250, d47249, d47248, d47247, d47246, d47245, d47244, d47243, d47242, d47241, d47240, d47239, d46863, d46458, d45904, d45496, d45172, d44968, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal47326 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d47326 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d47326, d47325, d47324, d47323, d47322, d47321, d47320, d47319, d47318, d47317, d47316, d47315, d47314, d47313, d47312, d47311, d47310, d47309, d47308, d47307, d47306, d47305, d47304, d47303, d47302, d47301, d47300, d47299, d47298, d47297, d47296, d47295, d47294, d47293, d47292, d47291, d47290, d47289, d47288, d47287, d47286, d47285, d47284, d47283, d46863, d46458, d45904, d45496, d45172, d44968, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal47371 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d47371 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d47371, d47370, d47369, d47368, d47367, d47366, d47365, d47364, d47363, d47362, d47361, d47360, d47359, d47358, d47357, d47356, d47355, d47354, d47353, d47352, d47351, d47350, d47349, d47348, d47347, d47346, d47345, d47344, d47343, d47342, d47341, d47340, d47339, d47338, d47337, d47336, d47335, d47334, d47333, d47332, d47331, d47330, d47329, d47328, d47327, d46458, d45904, d45496, d45172, d44968, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal47417 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d47417 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d47417, d47416, d47415, d47414, d47413, d47412, d47411, d47410, d47409, d47408, d47407, d47406, d47405, d47404, d47403, d47402, d47401, d47400, d47399, d47398, d47397, d47396, d47395, d47394, d47393, d47392, d47391, d47390, d47389, d47388, d47387, d47386, d47385, d47384, d47383, d47382, d47381, d47380, d47379, d47378, d47377, d47376, d47375, d47374, d47373, d47372, d45904, d45496, d45172, d44968, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal47464 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d47464 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d47464, d47463, d47462, d47461, d47460, d47459, d47458, d47457, d47456, d47455, d47454, d47453, d47452, d47451, d47450, d47449, d47448, d47447, d47446, d47445, d47444, d47443, d47442, d47441, d47440, d47439, d47438, d47437, d47436, d47435, d47434, d47433, d47432, d47431, d47430, d47429, d47428, d47427, d47426, d47425, d47424, d47423, d47422, d47421, d47420, d47419, d47418, d45496, d45172, d44968, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal47512 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d47512 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d47512, d47511, d47510, d47509, d47508, d47507, d47506, d47505, d47504, d47503, d47502, d47501, d47500, d47499, d47498, d47497, d47496, d47495, d47494, d47493, d47492, d47491, d47490, d47489, d47488, d47487, d47486, d47485, d47484, d47483, d47482, d47481, d47480, d47479, d47478, d47477, d47476, d47475, d47474, d47473, d47472, d47471, d47470, d47469, d47468, d47467, d47466, d47465, d45172, d44968, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal47561 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d47561 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d47561, d47560, d47559, d47558, d47557, d47556, d47555, d47554, d47553, d47552, d47551, d47550, d47549, d47548, d47547, d47546, d47545, d47544, d47543, d47542, d47541, d47540, d47539, d47538, d47537, d47536, d47535, d47534, d47533, d47532, d47531, d47530, d47529, d47528, d47527, d47526, d47525, d47524, d47523, d47522, d47521, d47520, d47519, d47518, d47517, d47516, d47515, d47514, d47513, d44968, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem goal47611 (p : Pattern) (empty : ∀ hole ∈ ([250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell), p (10000 + hole) = false) : d47611 p = 0 := by
  have h250 : p 10250 = false := empty 250 (by decide)
  have h251 : p 10251 = false := empty 251 (by decide)
  have h252 : p 10252 = false := empty 252 (by decide)
  have h253 : p 10253 = false := empty 253 (by decide)
  have h254 : p 10254 = false := empty 254 (by decide)
  have h255 : p 10255 = false := empty 255 (by decide)
  have h256 : p 10256 = false := empty 256 (by decide)
  have h257 : p 10257 = false := empty 257 (by decide)
  have h258 : p 10258 = false := empty 258 (by decide)
  have h259 : p 10259 = false := empty 259 (by decide)
  have h260 : p 10260 = false := empty 260 (by decide)
  simp only [d47611, d47610, d47609, d47608, d47607, d47606, d47605, d47604, d47603, d47602, d47601, d47600, d47599, d47598, d47597, d47596, d47595, d47594, d47593, d47592, d47591, d47590, d47589, d47588, d47587, d47586, d47585, d47584, d47583, d47582, d47581, d47580, d47579, d47578, d47577, d47576, d47575, d47574, d47573, d47572, d47571, d47570, d47569, d47568, d47567, d47566, d47565, d47564, d47563, d47562, d99, d0, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, Bool.false_eq_true, ↓reduceIte, ite_self]
theorem bonus_goal (hero : Cell) (p : Pattern) (empty : ∀ hole ∈ soko2_2.initial.holes, p (10000 + hole) = false) : bonus hero p = 0 := by
  unfold bonus
  simp only [goal0 p empty, goal2518 p empty, goal2671 p empty, goal2782 p empty, goal2895 p empty, goal3015 p empty, goal3142 p empty, goal3318 p empty, goal3496 p empty, goal3673 p empty, goal3842 p empty, goal4025 p empty, goal4334 p empty, goal4650 p empty, goal5349 p empty, goal5849 p empty, goal6737 p empty, goal7239 p empty, goal8234 p empty, goal9291 p empty, goal10648 p empty, goal12224 p empty, goal13979 p empty, goal15965 p empty, goal17560 p empty, goal18533 p empty, goal19737 p empty, goal20389 p empty, goal20891 p empty, goal23134 p empty, goal25101 p empty, goal27480 p empty, goal28738 p empty, goal30634 p empty, goal33212 p empty, goal36004 p empty, goal38812 p empty, goal40148 p empty, goal42245 p empty, goal44879 p empty, goal47282 p empty, goal47326 p empty, goal47371 p empty, goal47417 p empty, goal47464 p empty, goal47512 p empty, goal47561 p empty, goal47611 p empty, ite_self]
theorem initial_bonus : bonus soko2_2.initial.player (HazardPattern.combined 10000 soko2_2.initial) = 2 := by decide +kernel
end NetHack.Soko22Hazard87
