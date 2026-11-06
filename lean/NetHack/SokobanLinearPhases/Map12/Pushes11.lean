import NetHack.SokobanLinearPhases.Map12.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map12
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem subset11 : decide (crates 11 ⊆ crates 12) = true := by decide +kernel
theorem pushes11_part0 : ([29, 30, 56, 82, 105, 106, 108, 115] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part1 : ([116, 117, 131, 132, 133, 134, 135, 140] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part2 : ([141, 142, 143, 157, 158, 159, 160, 161] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part3 : ([163, 164, 166, 167, 168, 169, 184, 185] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part4 : ([186, 187, 189, 190, 191, 192, 193, 194] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part5 : ([210, 211, 212, 213, 214, 215, 216, 218] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part6 : ([219, 220, 236, 237, 238, 239, 241, 242] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part7 : ([244, 245, 246, 262, 263, 264, 265, 270] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part8 : ([271, 272, 288, 289, 290, 291, 292, 293] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part9 : ([294, 296, 297, 317, 318, 319, 320, 322] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part10 : ([345, 348, 370, 371, 372, 373, 374, 397] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
theorem pushes11_part11 : ([400] : List Cell).all (pushRow 11) = true := by
  try simp only [pushRow, subset11]
  decide +kernel
end NetHack.SokobanLinearPhases.Map12
