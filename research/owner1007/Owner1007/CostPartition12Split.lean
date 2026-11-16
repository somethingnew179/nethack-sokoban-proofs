import Owner1007.CostPartition12Factor
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
def owner1007_leftBonus (player : Cell) (p : Pattern) : Int :=
  if ([29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 55, 56, 76, 82, 102, 108, 128, 154, 180, 206, 232, 258, 284, 310, 336] : List Cell).contains player then d53 p else
  if ([105, 106, 131, 157] : List Cell).contains player then d105 p else
  if ([115, 116, 117, 142, 143, 169] : List Cell).contains player then d178 p else
  if ([132] : List Cell).contains player then d198 p else
  if ([133] : List Cell).contains player then d209 p else
  if ([134] : List Cell).contains player then d52 p else
  if ([135, 161] : List Cell).contains player then d226 p else
  if ([140, 163, 164, 166, 167, 184, 185, 189, 190, 191, 194, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 236, 237, 238, 239, 241, 242, 244, 245, 246, 262, 263, 264, 265, 270, 272, 288, 289, 290, 291, 292, 293, 294, 296, 297, 317, 318, 319, 320, 322, 345, 348, 370, 371, 372, 373, 374, 396, 397, 399, 400] : List Cell).contains player then d178 p else
  if ([141] : List Cell).contains player then d178 p else
  if ([158] : List Cell).contains player then d314 p else
  if ([159] : List Cell).contains player then d334 p else
  if ([160] : List Cell).contains player then d365 p else
  if ([168] : List Cell).contains player then d178 p else
  if ([186] : List Cell).contains player then d450 p else
  if ([187] : List Cell).contains player then d500 p else
  if ([192] : List Cell).contains player then d178 p else
  if ([193] : List Cell).contains player then d178 p else
  if ([271] : List Cell).contains player then d178 p else
  0
def owner1007_rightBonus (player : Cell) (p : Pattern) : Int :=
  if ([29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 55, 56, 76, 82, 102, 108, 128, 154, 180, 206, 232, 258, 284, 310, 336] : List Cell).contains player then d13 p else
  if ([105, 106, 131, 157] : List Cell).contains player then d13 p else
  if ([115, 116, 117, 142, 143, 169] : List Cell).contains player then d7 p else
  if ([132] : List Cell).contains player then d13 p else
  if ([133] : List Cell).contains player then d13 p else
  if ([134] : List Cell).contains player then d13 p else
  if ([135, 161] : List Cell).contains player then d13 p else
  if ([140, 163, 164, 166, 167, 184, 185, 189, 190, 191, 194, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 236, 237, 238, 239, 241, 242, 244, 245, 246, 262, 263, 264, 265, 270, 272, 288, 289, 290, 291, 292, 293, 294, 296, 297, 317, 318, 319, 320, 322, 345, 348, 370, 371, 372, 373, 374, 396, 397, 399, 400] : List Cell).contains player then d13 p else
  if ([141] : List Cell).contains player then d20 p else
  if ([158] : List Cell).contains player then d13 p else
  if ([159] : List Cell).contains player then d13 p else
  if ([160] : List Cell).contains player then d13 p else
  if ([168] : List Cell).contains player then d23 p else
  if ([186] : List Cell).contains player then d13 p else
  if ([187] : List Cell).contains player then d13 p else
  if ([192] : List Cell).contains player then d27 p else
  if ([193] : List Cell).contains player then d34 p else
  if ([271] : List Cell).contains player then d44 p else
  0
theorem owner1007_bonus_factor (player : Cell) (p : Pattern) :
    bonus player p = owner1007_leftBonus player p + owner1007_rightBonus player p := by
  by_cases h0 : ([29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 55, 56, 76, 82, 102, 108, 128, 154, 180, 206, 232, 258, 284, 310, 336] : List Cell).contains player = true
  · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_pos h0] using (owner1007_all_factor p).1
  · by_cases h1 : ([105, 106, 131, 157] : List Cell).contains player = true
    · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_pos h1] using (owner1007_all_factor p).2.1
    · by_cases h2 : ([115, 116, 117, 142, 143, 169] : List Cell).contains player = true
      · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_pos h2] using (owner1007_all_factor p).2.2.1
      · by_cases h3 : ([132] : List Cell).contains player = true
        · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_pos h3] using (owner1007_all_factor p).2.2.2.1
        · by_cases h4 : ([133] : List Cell).contains player = true
          · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4] using (owner1007_all_factor p).2.2.2.2.1
          · by_cases h5 : ([134] : List Cell).contains player = true
            · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5] using (owner1007_all_factor p).2.2.2.2.2.1
            · by_cases h6 : ([135, 161] : List Cell).contains player = true
              · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6] using (owner1007_all_factor p).2.2.2.2.2.2.1
              · by_cases h7 : ([140, 163, 164, 166, 167, 184, 185, 189, 190, 191, 194, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 236, 237, 238, 239, 241, 242, 244, 245, 246, 262, 263, 264, 265, 270, 272, 288, 289, 290, 291, 292, 293, 294, 296, 297, 317, 318, 319, 320, 322, 345, 348, 370, 371, 372, 373, 374, 396, 397, 399, 400] : List Cell).contains player = true
                · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7] using (owner1007_all_factor p).2.2.2.2.2.2.2.1
                · by_cases h8 : ([141] : List Cell).contains player = true
                  · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.1
                  · by_cases h9 : ([158] : List Cell).contains player = true
                    · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos h9] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.2.1
                    · by_cases h10 : ([159] : List Cell).contains player = true
                      · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_pos h10] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.2.2.1
                      · by_cases h11 : ([160] : List Cell).contains player = true
                        · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_pos h11] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.2.2.2.1
                        · by_cases h12 : ([168] : List Cell).contains player = true
                          · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_pos h12] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.2.2.2.2.1
                          · by_cases h13 : ([186] : List Cell).contains player = true
                            · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_pos h13] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.2.2.2.2.2.1
                            · by_cases h14 : ([187] : List Cell).contains player = true
                              · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_pos h14] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                              · by_cases h15 : ([192] : List Cell).contains player = true
                                · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_neg h14, if_pos h15] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                                · by_cases h16 : ([193] : List Cell).contains player = true
                                  · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_neg h14, if_neg h15, if_pos h16] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                                  · by_cases h17 : ([271] : List Cell).contains player = true
                                    · simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_neg h14, if_neg h15, if_neg h16, if_pos h17] using (owner1007_all_factor p).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                                    · simp only [bonus, owner1007_leftBonus, owner1007_rightBonus, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_neg h14, if_neg h15, if_neg h16, if_neg h17, Int.add_zero]
theorem owner1007_right13_formula (p : Pattern) :
    d13 p = (if p 192 && p 193 then (2 : Int) else 0) +
      (if p 141 && p 168 && p 271 then (1 : Int) else 0) := by
  cases h141 : p 141 <;> cases h168 : p 168 <;>
    cases h192 : p 192 <;> cases h193 : p 193 <;>
    cases h271 : p 271 <;>
    simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,
      h141,h168,h192,h193,h271]
#print axioms owner1007_bonus_factor
#print axioms owner1007_right13_formula
end NetHack.Sokoban12CostPartition
