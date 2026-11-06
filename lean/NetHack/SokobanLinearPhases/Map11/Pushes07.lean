import NetHack.SokobanLinearPhases.Map11.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem subset07 : decide (crates 7 ⊆ crates 8) = true := by decide +kernel
theorem pushes07_part0 : ([27, 28, 29, 30, 31, 32, 33, 59] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part1 : ([85, 106, 107, 108, 109, 110, 111, 112] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part2 : ([113, 114, 115, 116, 132, 133, 134, 135] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part3 : ([136, 137, 138, 139, 140, 141, 142, 164] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part4 : ([183, 184, 185, 186, 187, 188, 189, 190] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part5 : ([191, 192, 193, 194, 209, 210, 211, 212] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part6 : ([213, 214, 215, 216, 217, 218, 219, 220] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part7 : ([239, 262, 263, 264, 265, 266, 267, 268] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part8 : ([269, 270, 271, 288, 289, 290, 291, 292] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part9 : ([293, 294, 295, 296, 297, 314, 315, 316] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part10 : ([317, 318, 319, 320, 321, 322, 345, 365] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part11 : ([366, 367, 368, 369, 370, 371, 372, 391] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part12 : ([392, 393, 394, 395, 396, 397, 398, 417] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
theorem pushes07_part13 : ([418, 419] : List Cell).all (pushRow 7) = true := by
  try simp only [pushRow, subset07]
  decide +kernel
end NetHack.SokobanLinearPhases.Map11
