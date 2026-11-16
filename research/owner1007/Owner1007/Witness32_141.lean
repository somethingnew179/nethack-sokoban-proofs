import NetHack.Sokoban.Maps
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Owner1007.Witness32_141
open NetHack.Sokoban
def block0 : List Dir := [.southWest, .southWest, .south, .south, .south, .east, .north, .east, .east, .west, .west, .northWest, .north, .northEast, .east, .east, .east, .east, .east, .east, .south, .south, .east, .northWest, .northWest, .west, .west, .west, .west, .west, .southWest, .south]
def state0 : State := {player := 105, boulders := [114, 138, 135, 106, 159, 80, 139, 161, 188, 211, 215, 239, 244, 267, 270, 289], holes := [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem checked0 : run soko3_2.board soko3_2.initial block0 = some ⟨state0, 6, 32⟩ := by decide +kernel
def prefix0 : List Dir := block0
theorem prefix_checked0 : run soko3_2.board soko3_2.initial prefix0 = some ⟨state0, 6, 32⟩ := checked0
def block1 : List Dir := [.south, .south, .south, .southEast, .east, .east, .east, .south, .south, .east, .southEast, .east, .northEast, .northWest, .west, .south, .west, .northWest, .northWest, .west, .west, .northWest, .northEast, .northEast, .east, .northEast, .southEast, .south, .southEast, .south, .south, .north]
def state1 : State := {player := 215, boulders := [267, 293, 291, 214, 114, 138, 135, 106, 159, 80, 139, 161, 188, 244, 270, 289], holes := [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem checked1 : run soko3_2.board state0 block1 = some ⟨state1, 8, 32⟩ := by decide +kernel
def prefix1 : List Dir := prefix0 ++ block1
theorem prefix_checked1 : run soko3_2.board soko3_2.initial prefix1 = some ⟨state1, 14, 64⟩ :=
  run_append_of _ _ prefix0 block1 ⟨state0, 6, 32⟩ ⟨state1, 8, 32⟩ prefix_checked0 checked1
def block2 : List Dir := [.north, .north, .northWest, .northWest, .west, .southWest, .southWest, .southWest, .southEast, .east, .east, .southEast, .south, .southEast, .east, .east, .west, .northWest, .northWest, .northWest, .west, .west, .northWest, .northEast, .northEast, .east, .northEast, .southEast, .south, .southEast, .south, .southEast]
def state2 : State := {player := 242, boulders := [295, 267, 291, 214, 114, 138, 135, 106, 159, 80, 139, 161, 188, 244, 270, 289], holes := [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem checked2 : run soko3_2.board state1 block2 = some ⟨state2, 2, 32⟩ := by decide +kernel
def prefix2 : List Dir := prefix1 ++ block2
theorem prefix_checked2 : run soko3_2.board soko3_2.initial prefix2 = some ⟨state2, 16, 96⟩ :=
  run_append_of _ _ prefix1 block2 ⟨state1, 14, 64⟩ ⟨state2, 2, 32⟩ prefix_checked1 checked2
def block3 : List Dir := [.southEast, .east, .northEast, .west, .north, .north, .northWest, .north, .west, .north, .north, .northWest, .west, .west, .west, .west, .west, .southWest, .south, .southEast, .east, .east, .northEast, .southEast, .south, .southEast, .south, .southEast, .east, .northWest, .northWest, .north]
def state3 : State := {player := 163, boulders := [244, 137, 113, 295, 267, 291, 214, 114, 135, 106, 159, 80, 161, 188, 289], holes := [273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem checked3 : run soko3_2.board state2 block3 = some ⟨state3, 5, 32⟩ := by decide +kernel
def prefix3 : List Dir := prefix2 ++ block3
theorem prefix_checked3 : run soko3_2.board soko3_2.initial prefix3 = some ⟨state3, 21, 128⟩ :=
  run_append_of _ _ prefix2 block3 ⟨state2, 16, 96⟩ ⟨state3, 5, 32⟩ prefix_checked2 checked3
def block4 : List Dir := [.northWest, .northWest, .west, .southWest, .west, .northWest, .north, .northEast, .east, .east, .east, .east, .east, .southEast, .south, .south, .southEast, .southEast, .south, .south, .southWest, .east, .northWest, .northWest, .northWest, .north, .northWest, .northWest, .west, .southWest, .southWest, .southWest]
def state4 : State := {player := 183, boulders := [137, 113, 295, 267, 291, 214, 114, 135, 106, 159, 80, 161, 188, 289], holes := [274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem checked4 : run soko3_2.board state3 block4 = some ⟨state4, 2, 32⟩ := by decide +kernel
def prefix4 : List Dir := prefix3 ++ block4
theorem prefix_checked4 : run soko3_2.board soko3_2.initial prefix4 = some ⟨state4, 23, 160⟩ :=
  run_append_of _ _ prefix3 block4 ⟨state3, 21, 128⟩ ⟨state4, 2, 32⟩ prefix_checked3 checked4
def block5 : List Dir := [.southEast, .east, .east, .southEast, .southEast, .southEast, .east, .southEast, .north, .north, .southWest, .west, .northWest, .northWest, .northWest, .west, .west, .northWest, .northEast, .northEast, .east, .northEast, .southEast, .south, .southEast, .south, .southEast, .east, .northWest, .northWest, .north, .northWest]
def state5 : State := {player := 136, boulders := [244, 137, 113, 267, 291, 214, 114, 135, 106, 159, 80, 161, 188, 289], holes := [274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem checked5 : run soko3_2.board state4 block5 = some ⟨state5, 3, 32⟩ := by decide +kernel
def prefix5 : List Dir := prefix4 ++ block5
theorem prefix_checked5 : run soko3_2.board soko3_2.initial prefix5 = some ⟨state5, 26, 192⟩ :=
  run_append_of _ _ prefix4 block5 ⟨state4, 23, 160⟩ ⟨state5, 3, 32⟩ prefix_checked4 checked5
def block6 : List Dir := [.northWest, .west, .southWest, .west, .northWest, .north, .northEast, .east, .east, .east, .east, .east, .southEast, .south, .south, .southEast, .southEast, .south, .south, .southWest, .east, .west, .northWest, .west, .south, .southWest, .east, .east, .southEast, .north, .north, .southWest]
def state6 : State := {player := 294, boulders := [243, 137, 113, 291, 214, 114, 135, 106, 159, 80, 161, 188, 289], holes := [275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem checked6 : run soko3_2.board state5 block6 = some ⟨state6, 7, 32⟩ := by decide +kernel
def prefix6 : List Dir := prefix5 ++ block6
theorem prefix_checked6 : run soko3_2.board soko3_2.initial prefix6 = some ⟨state6, 33, 224⟩ :=
  run_append_of _ _ prefix5 block6 ⟨state5, 26, 192⟩ ⟨state6, 7, 32⟩ prefix_checked5 checked6
def block7 : List Dir := [.northWest, .northEast, .east, .northWest, .northWest, .north, .northWest, .northWest, .west, .southWest, .west, .northWest, .north, .northEast, .east, .east, .east, .east, .east, .southEast, .south, .south, .southEast, .southEast, .south, .south, .southWest, .east, .west, .northWest, .west, .southWest]
def state7 : State := {player := 266, boulders := [137, 113, 291, 214, 114, 135, 106, 159, 80, 161, 188, 289], holes := [276, 277, 278, 279, 280, 281, 282, 283]}
theorem checked7 : run soko3_2.board state6 block7 = some ⟨state7, 3, 32⟩ := by decide +kernel
def prefix7 : List Dir := prefix6 ++ block7
theorem prefix_checked7 : run soko3_2.board soko3_2.initial prefix7 = some ⟨state7, 36, 256⟩ :=
  run_append_of _ _ prefix6 block7 ⟨state6, 33, 224⟩ ⟨state7, 3, 32⟩ prefix_checked6 checked7
def block8 : List Dir := [.northWest, .north, .east, .west, .west, .west, .west, .northWest, .northEast, .northEast, .east, .northEast, .southEast, .south, .southEast, .south, .south, .south, .southWest, .east, .east, .southEast, .north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northWest]
def state8 : State := {player := 136, boulders := [244, 137, 113, 291, 114, 135, 106, 159, 80, 161, 188, 289], holes := [276, 277, 278, 279, 280, 281, 282, 283]}
theorem checked8 : run soko3_2.board state7 block8 = some ⟨state8, 9, 32⟩ := by decide +kernel
def prefix8 : List Dir := prefix7 ++ block8
theorem prefix_checked8 : run soko3_2.board soko3_2.initial prefix8 = some ⟨state8, 45, 288⟩ :=
  run_append_of _ _ prefix7 block8 ⟨state7, 36, 256⟩ ⟨state8, 9, 32⟩ prefix_checked7 checked8
def block9 : List Dir := [.northWest, .west, .southWest, .west, .northWest, .north, .northEast, .east, .east, .east, .east, .east, .southEast, .south, .south, .southEast, .southEast, .south, .south, .southWest, .east, .northWest, .northWest, .northWest, .northWest, .south, .southEast, .south, .southWest, .northWest, .north, .east]
def state9 : State := {player := 214, boulders := [215, 137, 113, 291, 114, 135, 106, 159, 80, 161, 289], holes := [277, 278, 279, 280, 281, 282, 283]}
theorem checked9 : run soko3_2.board state8 block9 = some ⟨state9, 4, 32⟩ := by decide +kernel
def prefix9 : List Dir := prefix8 ++ block9
theorem prefix_checked9 : run soko3_2.board soko3_2.initial prefix9 = some ⟨state9, 49, 320⟩ :=
  run_append_of _ _ prefix8 block9 ⟨state8, 45, 288⟩ ⟨state9, 4, 32⟩ prefix_checked8 checked9
def block10 : List Dir := [.northEast, .south, .south, .south, .southWest, .east, .east, .southEast, .north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northWest, .northWest, .west, .southWest, .west, .northWest, .north, .northEast, .east, .east, .east, .east, .east, .southEast, .south]
def state10 : State := {player := 112, boulders := [244, 137, 113, 291, 114, 135, 106, 159, 80, 161, 289], holes := [277, 278, 279, 280, 281, 282, 283]}
theorem checked10 : run soko3_2.board state9 block10 = some ⟨state10, 8, 32⟩ := by decide +kernel
def prefix10 : List Dir := prefix9 ++ block10
theorem prefix_checked10 : run soko3_2.board soko3_2.initial prefix10 = some ⟨state10, 57, 352⟩ :=
  run_append_of _ _ prefix9 block10 ⟨state9, 49, 320⟩ ⟨state10, 8, 32⟩ prefix_checked9 checked10
def block11 : List Dir := [.south, .southEast, .southEast, .south, .south, .southWest, .east, .north, .north, .north, .northWest, .northWest, .west, .south, .southWest, .southWest, .west, .west, .west, .northWest, .northEast, .northEast, .east, .northEast, .east, .south, .south, .south, .southEast, .south, .southWest, .northWest]
def state11 : State := {player := 239, boulders := [214, 113, 291, 114, 135, 106, 159, 80, 161, 289], holes := [278, 279, 280, 281, 282, 283]}
theorem checked11 : run soko3_2.board state10 block11 = some ⟨state11, 6, 32⟩ := by decide +kernel
def prefix11 : List Dir := prefix10 ++ block11
theorem prefix_checked11 : run soko3_2.board soko3_2.initial prefix11 = some ⟨state11, 63, 384⟩ :=
  run_append_of _ _ prefix10 block11 ⟨state10, 57, 352⟩ ⟨state11, 6, 32⟩ prefix_checked10 checked11
def block12 : List Dir := [.north, .east, .northEast, .south, .south, .south, .southWest, .east, .east, .southEast, .north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .east, .northWest, .northWest, .northWest, .north, .northWest, .northWest]
def state12 : State := {player := 109, boulders := [113, 291, 114, 135, 106, 159, 80, 161, 289], holes := [279, 280, 281, 282, 283]}
theorem checked12 : run soko3_2.board state11 block12 = some ⟨state12, 11, 32⟩ := by decide +kernel
def prefix12 : List Dir := prefix11 ++ block12
theorem prefix_checked12 : run soko3_2.board soko3_2.initial prefix12 = some ⟨state12, 74, 416⟩ :=
  run_append_of _ _ prefix11 block12 ⟨state11, 63, 384⟩ ⟨state12, 11, 32⟩ prefix_checked11 checked12
def block13 : List Dir := [.southWest, .east, .northEast, .south, .south, .south, .southEast, .south, .southWest, .northWest, .north, .east, .northEast, .south, .south, .south, .southWest, .east, .east, .southEast, .north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast]
def state13 : State := {player := 192, boulders := [244, 113, 291, 114, 106, 159, 80, 161, 289], holes := [279, 280, 281, 282, 283]}
theorem checked13 : run soko3_2.board state12 block13 = some ⟨state13, 13, 32⟩ := by decide +kernel
def prefix13 : List Dir := prefix12 ++ block13
theorem prefix_checked13 : run soko3_2.board soko3_2.initial prefix13 = some ⟨state13, 87, 448⟩ :=
  run_append_of _ _ prefix12 block13 ⟨state12, 74, 416⟩ ⟨state13, 13, 32⟩ prefix_checked12 checked13
def block14 : List Dir := [.south, .south, .southWest, .east, .northWest, .northWest, .northWest, .northWest, .northWest, .southWest, .east, .northEast, .south, .south, .southEast, .south, .southWest, .northWest, .north, .east, .northEast, .south, .south, .south, .southWest, .east, .east, .southEast, .north, .north, .southWest, .northWest]
def state14 : State := {player := 267, boulders := [243, 113, 291, 114, 106, 159, 80, 289], holes := [280, 281, 282, 283]}
theorem checked14 : run soko3_2.board state13 block14 = some ⟨state14, 13, 32⟩ := by decide +kernel
def prefix14 : List Dir := prefix13 ++ block14
theorem prefix_checked14 : run soko3_2.board soko3_2.initial prefix14 = some ⟨state14, 100, 480⟩ :=
  run_append_of _ _ prefix13 block14 ⟨state13, 87, 448⟩ ⟨state14, 13, 32⟩ prefix_checked13 checked14
def block15 : List Dir := [.northEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .east, .west, .northWest, .northWest, .northWest, .northWest, .west, .northWest, .southWest, .east, .east, .east, .northEast, .south, .south, .southEast, .south, .southWest, .northWest, .north, .east]
def state15 : State := {player := 214, boulders := [215, 113, 291, 114, 106, 80, 289], holes := [281, 282, 283]}
theorem checked15 : run soko3_2.board state14 block15 = some ⟨state15, 9, 32⟩ := by decide +kernel
def prefix15 : List Dir := prefix14 ++ block15
theorem prefix_checked15 : run soko3_2.board soko3_2.initial prefix15 = some ⟨state15, 109, 512⟩ :=
  run_append_of _ _ prefix14 block15 ⟨state14, 100, 480⟩ ⟨state15, 9, 32⟩ prefix_checked14 checked15
def block16 : List Dir := [.northEast, .south, .south, .south, .southWest, .east, .east, .southEast, .north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .east, .west, .northWest, .southWest, .southWest, .southWest, .north, .northEast, .northEast]
def state16 : State := {player := 241, boulders := [265, 113, 114, 106, 80, 289], holes := [282, 283]}
theorem checked16 : run soko3_2.board state15 block16 = some ⟨state16, 11, 32⟩ := by decide +kernel
def prefix16 : List Dir := prefix15 ++ block16
theorem prefix_checked16 : run soko3_2.board soko3_2.initial prefix16 = some ⟨state16, 120, 544⟩ :=
  run_append_of _ _ prefix15 block16 ⟨state15, 109, 512⟩ ⟨state16, 11, 32⟩ prefix_checked15 checked16
def block17 : List Dir := [.northWest, .west, .west, .west, .west, .southWest, .south, .southEast, .east, .east, .east, .east, .east, .east, .southEast, .north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .east, .west]
def state17 : State := {player := 269, boulders := [265, 113, 114, 106, 80], holes := [283]}
theorem checked17 : run soko3_2.board state16 block17 = some ⟨state17, 11, 32⟩ := by decide +kernel
def prefix17 : List Dir := prefix16 ++ block17
theorem prefix_checked17 : run soko3_2.board soko3_2.initial prefix17 = some ⟨state17, 131, 576⟩ :=
  run_append_of _ _ prefix16 block17 ⟨state16, 120, 544⟩ ⟨state17, 11, 32⟩ prefix_checked16 checked17
def block18 : List Dir := [.northWest, .west, .northWest, .southWest, .south, .north, .northWest, .west, .west, .southWest, .southEast, .east, .southEast, .east, .east, .east, .east, .southEast, .north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south]
def state18 : State := {player := 244, boulders := [270, 113, 114, 106, 80], holes := [283]}
theorem checked18 : run soko3_2.board state17 block18 = some ⟨state18, 9, 32⟩ := by decide +kernel
def prefix18 : List Dir := prefix17 ++ block18
theorem prefix_checked18 : run soko3_2.board soko3_2.initial prefix18 = some ⟨state18, 140, 608⟩ :=
  run_append_of _ _ prefix17 block18 ⟨state17, 131, 576⟩ ⟨state18, 9, 32⟩ prefix_checked17 checked18
def block19 : List Dir := [.southWest, .east]
def state19 : State := {player := 270, boulders := [113, 114, 106, 80], holes := []}
theorem checked19 : run soko3_2.board state18 block19 = some ⟨state19, 1, 2⟩ := by decide +kernel
def prefix19 : List Dir := prefix18 ++ block19
theorem prefix_checked19 : run soko3_2.board soko3_2.initial prefix19 = some ⟨state19, 141, 610⟩ :=
  run_append_of _ _ prefix18 block19 ⟨state18, 140, 608⟩ ⟨state19, 1, 2⟩ prefix_checked18 checked19
def path : List Dir := prefix19
def finalState : State := state19
theorem solution : Trace soko3_2.board soko3_2.initial path finalState 141 610 ∧ Goal finalState :=
  ⟨run_sound _ _ _ _ prefix_checked19, rfl⟩
#print axioms solution
end Owner1007.Witness32_141
