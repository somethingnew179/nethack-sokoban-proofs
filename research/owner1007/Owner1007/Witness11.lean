import NetHack.Sokoban.Maps
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Owner1007.Witness11
open NetHack.Sokoban
def block0 : List Dir := [.east, .east, .east, .east, .southEast, .southEast, .south, .southEast, .south, .southWest, .southWest, .southWest, .south, .west, .east, .southEast, .east, .east, .east, .southWest, .southWest, .southWest, .west, .west, .southWest, .northWest, .east, .east, .east, .southEast, .northEast, .north]
def state0 : State := {player := 345, boulders := [370, 296, 263, 133, 135, 137, 139, 141, 186, 212, 188, 191, 193, 315, 317, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked0 : run soko1_1.board soko1_1.initial block0 = some ⟨state0, 7, 32⟩ := by decide +kernel
def prefix0 : List Dir := block0
theorem prefix_checked0 : run soko1_1.board soko1_1.initial prefix0 = some ⟨state0, 7, 32⟩ := checked0
def block1 : List Dir := [.northWest, .northWest, .southWest, .east, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .west, .northWest, .southWest, .southEast, .north, .northWest, .east, .southEast, .east, .east, .northEast, .north, .north, .northWest, .northWest, .north, .north, .north, .west]
def state1 : State := {player := 186, boulders := [185, 368, 370, 296, 263, 133, 135, 137, 139, 141, 212, 188, 191, 193, 315, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked1 : run soko1_1.board state0 block1 = some ⟨state1, 12, 32⟩ := by decide +kernel
def prefix1 : List Dir := prefix0 ++ block1
theorem prefix_checked1 : run soko1_1.board soko1_1.initial prefix1 = some ⟨state1, 19, 64⟩ :=
  run_append_of _ _ prefix0 block1 ⟨state0, 7, 32⟩ ⟨state1, 12, 32⟩ prefix_checked0 checked1
def block2 : List Dir := [.west, .south, .east, .northEast, .south, .south, .south, .south, .southWest, .east, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .northEast, .north, .north, .northWest, .northWest]
def state2 : State := {player := 265, boulders := [366, 184, 368, 370, 296, 263, 133, 135, 137, 139, 141, 188, 191, 193, 315, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked2 : run soko1_1.board state1 block2 = some ⟨state2, 17, 32⟩ := by decide +kernel
def prefix2 : List Dir := prefix1 ++ block2
theorem prefix_checked2 : run soko1_1.board soko1_1.initial prefix2 = some ⟨state2, 36, 96⟩ :=
  run_append_of _ _ prefix1 block2 ⟨state1, 19, 64⟩ ⟨state2, 17, 32⟩ prefix_checked1 checked2
def block3 : List Dir := [.north, .northEast, .northEast, .west, .west, .east, .east, .east, .southEast, .northEast, .west, .west, .north, .north, .northEast, .southEast, .west, .northWest, .south, .south, .south, .southEast, .west, .west, .west, .northWest, .south, .south, .south, .southWest, .east, .north]
def state3 : State := {player := 265, boulders := [292, 189, 186, 366, 184, 368, 370, 296, 263, 133, 135, 137, 141, 193, 315, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked3 : run soko1_1.board state2 block3 = some ⟨state3, 15, 32⟩ := by decide +kernel
def prefix3 : List Dir := prefix2 ++ block3
theorem prefix_checked3 : run soko1_1.board soko1_1.initial prefix3 = some ⟨state3, 51, 128⟩ :=
  run_append_of _ _ prefix2 block3 ⟨state2, 36, 96⟩ ⟨state3, 15, 32⟩ prefix_checked2 checked3
def block4 : List Dir := [.north, .northEast, .east, .northEast, .north, .north, .northWest, .southWest, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .northWest, .south, .south, .south, .north, .north, .northEast, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest]
def state4 : State := {player := 137, boulders := [111, 291, 292, 186, 366, 184, 368, 370, 296, 263, 133, 135, 141, 193, 315, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked4 : run soko1_1.board state3 block4 = some ⟨state4, 15, 32⟩ := by decide +kernel
def prefix4 : List Dir := prefix3 ++ block4
theorem prefix_checked4 : run soko1_1.board soko1_1.initial prefix4 = some ⟨state4, 66, 160⟩ :=
  run_append_of _ _ prefix3 block4 ⟨state3, 51, 128⟩ ⟨state4, 15, 32⟩ prefix_checked3 checked4
def block5 : List Dir := [.north, .north, .north, .south, .south, .south, .southEast, .southWest, .west, .west, .southWest, .northWest, .east, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south]
def state5 : State := {player := 137, boulders := [291, 292, 366, 184, 368, 370, 296, 263, 133, 135, 141, 193, 315, 266, 268, 321], holes := [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked5 : run soko1_1.board state4 block5 = some ⟨state5, 15, 32⟩ := by decide +kernel
def prefix5 : List Dir := prefix4 ++ block5
theorem prefix_checked5 : run soko1_1.board soko1_1.initial prefix5 = some ⟨state5, 81, 192⟩ :=
  run_append_of _ _ prefix4 block5 ⟨state4, 66, 160⟩ ⟨state5, 15, 32⟩ prefix_checked4 checked5
def block6 : List Dir := [.southEast, .southWest, .west, .west, .west, .west, .southWest, .northWest, .east, .east, .east, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southEast]
def state6 : State := {player := 191, boulders := [291, 292, 366, 368, 370, 296, 263, 133, 135, 141, 193, 315, 266, 268, 321], holes := [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked6 : run soko1_1.board state5 block6 = some ⟨state6, 14, 32⟩ := by decide +kernel
def prefix6 : List Dir := prefix5 ++ block6
theorem prefix_checked6 : run soko1_1.board soko1_1.initial prefix6 = some ⟨state6, 95, 224⟩ :=
  run_append_of _ _ prefix5 block6 ⟨state5, 81, 192⟩ ⟨state6, 14, 32⟩ prefix_checked5 checked6
def block7 : List Dir := [.east, .southEast, .northEast, .west, .west, .west, .southWest, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .south, .southWest, .southEast, .north, .north, .north]
def state7 : State := {player := 239, boulders := [213, 292, 366, 368, 370, 296, 263, 133, 135, 141, 315, 266, 268, 321], holes := [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked7 : run soko1_1.board state6 block7 = some ⟨state7, 14, 32⟩ := by decide +kernel
def prefix7 : List Dir := prefix6 ++ block7
theorem prefix_checked7 : run soko1_1.board soko1_1.initial prefix7 = some ⟨state7, 109, 256⟩ :=
  run_append_of _ _ prefix6 block7 ⟨state6, 95, 224⟩ ⟨state7, 14, 32⟩ prefix_checked6 checked7
def block8 : List Dir := [.north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .south, .south, .southEast, .northEast, .west, .southWest, .north]
def state8 : State := {player := 291, boulders := [265, 366, 368, 370, 296, 263, 133, 135, 141, 315, 266, 268, 321], holes := [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked8 : run soko1_1.board state7 block8 = some ⟨state8, 14, 32⟩ := by decide +kernel
def prefix8 : List Dir := prefix7 ++ block8
theorem prefix_checked8 : run soko1_1.board soko1_1.initial prefix8 = some ⟨state8, 123, 288⟩ :=
  run_append_of _ _ prefix7 block8 ⟨state7, 109, 256⟩ ⟨state8, 14, 32⟩ prefix_checked7 checked8
def block9 : List Dir := [.north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .southWest, .southWest, .northWest, .east, .east]
def state9 : State := {player := 264, boulders := [265, 366, 368, 370, 296, 133, 135, 141, 315, 266, 268, 321], holes := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked9 : run soko1_1.board state8 block9 = some ⟨state9, 16, 32⟩ := by decide +kernel
def prefix9 : List Dir := prefix8 ++ block9
theorem prefix_checked9 : run soko1_1.board soko1_1.initial prefix9 = some ⟨state9, 139, 320⟩ :=
  run_append_of _ _ prefix8 block9 ⟨state8, 123, 288⟩ ⟨state9, 16, 32⟩ prefix_checked8 checked9
def block10 : List Dir := [.southEast, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .south, .southEast, .northEast, .west]
def state10 : State := {player := 266, boulders := [265, 366, 368, 370, 296, 133, 135, 141, 315, 268, 321], holes := [41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked10 : run soko1_1.board state9 block10 = some ⟨state10, 15, 32⟩ := by decide +kernel
def prefix10 : List Dir := prefix9 ++ block10
theorem prefix_checked10 : run soko1_1.board soko1_1.initial prefix10 = some ⟨state10, 154, 352⟩ :=
  run_append_of _ _ prefix9 block10 ⟨state9, 139, 320⟩ ⟨state10, 15, 32⟩ prefix_checked9 checked10
def block11 : List Dir := [.southWest, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .southEast, .east, .southEast, .northEast]
def state11 : State := {player := 269, boulders := [366, 368, 370, 296, 133, 135, 141, 315, 268, 321], holes := [42, 43, 44, 45, 46, 47, 48, 49]}
theorem checked11 : run soko1_1.board state10 block11 = some ⟨state11, 14, 32⟩ := by decide +kernel
def prefix11 : List Dir := prefix10 ++ block11
theorem prefix_checked11 : run soko1_1.board soko1_1.initial prefix11 = some ⟨state11, 168, 384⟩ :=
  run_append_of _ _ prefix10 block11 ⟨state10, 154, 352⟩ ⟨state11, 14, 32⟩ prefix_checked10 checked11
def block12 : List Dir := [.west, .west, .west, .southWest, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .southEast]
def state12 : State := {player := 266, boulders := [366, 368, 370, 296, 133, 135, 141, 315, 321], holes := [43, 44, 45, 46, 47, 48, 49]}
theorem checked12 : run soko1_1.board state11 block12 = some ⟨state12, 17, 32⟩ := by decide +kernel
def prefix12 : List Dir := prefix11 ++ block12
theorem prefix_checked12 : run soko1_1.board soko1_1.initial prefix12 = some ⟨state12, 185, 416⟩ :=
  run_append_of _ _ prefix11 block12 ⟨state11, 168, 384⟩ ⟨state12, 17, 32⟩ prefix_checked11 checked12
def block13 : List Dir := [.east, .east, .east, .east, .southEast, .west, .west, .west, .west, .west, .southWest, .north, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south]
def state13 : State := {player := 59, boulders := [366, 368, 370, 133, 135, 141, 315, 321], holes := [44, 45, 46, 47, 48, 49]}
theorem checked13 : run soko1_1.board state12 block13 = some ⟨state13, 20, 32⟩ := by decide +kernel
def prefix13 : List Dir := prefix12 ++ block13
theorem prefix_checked13 : run soko1_1.board soko1_1.initial prefix13 = some ⟨state13, 205, 448⟩ :=
  run_append_of _ _ prefix12 block13 ⟨state12, 185, 416⟩ ⟨state13, 20, 32⟩ prefix_checked12 checked13
def block14 : List Dir := [.south, .south, .south, .southEast, .southWest, .southWest, .southWest, .south, .south, .southEast, .southEast, .south, .southWest, .northWest, .east, .southEast, .north, .north, .north, .north, .northEast, .west, .west, .southWest, .north, .north, .north, .northWest, .east, .east, .east, .southEast]
def state14 : State := {player := 216, boulders := [190, 366, 368, 133, 135, 141, 315, 321], holes := [44, 45, 46, 47, 48, 49]}
theorem checked14 : run soko1_1.board state13 block14 = some ⟨state14, 13, 32⟩ := by decide +kernel
def prefix14 : List Dir := prefix13 ++ block14
theorem prefix_checked14 : run soko1_1.board soko1_1.initial prefix14 = some ⟨state14, 218, 480⟩ :=
  run_append_of _ _ prefix13 block14 ⟨state13, 205, 448⟩ ⟨state14, 13, 32⟩ prefix_checked13 checked14
def block15 : List Dir := [.north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .south, .south, .southEast, .southEast, .southWest, .west, .southWest, .northWest, .east, .east, .east, .southEast, .north]
def state15 : State := {player := 371, boulders := [345, 366, 133, 135, 141, 315, 321], holes := [45, 46, 47, 48, 49]}
theorem checked15 : run soko1_1.board state14 block15 = some ⟨state15, 12, 32⟩ := by decide +kernel
def prefix15 : List Dir := prefix14 ++ block15
theorem prefix_checked15 : run soko1_1.board soko1_1.initial prefix15 = some ⟨state15, 230, 512⟩ :=
  run_append_of _ _ prefix14 block15 ⟨state14, 218, 480⟩ ⟨state15, 12, 32⟩ prefix_checked14 checked15
def block16 : List Dir := [.north, .north, .north, .northEast, .west, .west, .southWest, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest]
def state16 : State := {player := 189, boulders := [366, 133, 135, 141, 315, 321], holes := [46, 47, 48, 49]}
theorem checked16 : run soko1_1.board state15 block16 = some ⟨state16, 19, 32⟩ := by decide +kernel
def prefix16 : List Dir := prefix15 ++ block16
theorem prefix_checked16 : run soko1_1.board soko1_1.initial prefix16 = some ⟨state16, 249, 544⟩ :=
  run_append_of _ _ prefix15 block16 ⟨state15, 230, 512⟩ ⟨state16, 19, 32⟩ prefix_checked15 checked16
def block17 : List Dir := [.southWest, .southWest, .south, .south, .southEast, .southEast, .southWest, .west, .west, .west, .southWest, .northWest, .east, .east, .east, .east, .east, .southEast, .north, .north, .north, .north, .northEast, .west, .west, .southWest, .north, .north, .north, .northWest, .east, .east]
def state17 : State := {player := 188, boulders := [189, 133, 135, 141, 315, 321], holes := [46, 47, 48, 49]}
theorem checked17 : run soko1_1.board state16 block17 = some ⟨state17, 16, 32⟩ := by decide +kernel
def prefix17 : List Dir := prefix16 ++ block17
theorem prefix_checked17 : run soko1_1.board soko1_1.initial prefix17 = some ⟨state17, 265, 576⟩ :=
  run_append_of _ _ prefix16 block17 ⟨state16, 249, 544⟩ ⟨state17, 16, 32⟩ prefix_checked16 checked17
def block18 : List Dir := [.east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .southWest, .west, .southWest, .east, .east, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .northWest, .south, .south]
def state18 : State := {player := 239, boulders := [265, 133, 141, 315, 321], holes := [47, 48, 49]}
theorem checked18 : run soko1_1.board state17 block18 = some ⟨state18, 20, 32⟩ := by decide +kernel
def prefix18 : List Dir := prefix17 ++ block18
theorem prefix_checked18 : run soko1_1.board soko1_1.initial prefix18 = some ⟨state18, 285, 608⟩ :=
  run_append_of _ _ prefix17 block18 ⟨state17, 265, 576⟩ ⟨state18, 20, 32⟩ prefix_checked17 checked18
def block19 : List Dir := [.south, .southEast, .southWest, .north, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .southWest, .west, .west, .west, .southWest, .east, .east]
def state19 : State := {player := 134, boulders := [135, 141, 315, 321], holes := [48, 49]}
theorem checked19 : run soko1_1.board state18 block19 = some ⟨state19, 18, 32⟩ := by decide +kernel
def prefix19 : List Dir := prefix18 ++ block19
theorem prefix_checked19 : run soko1_1.board soko1_1.initial prefix19 = some ⟨state19, 303, 640⟩ :=
  run_append_of _ _ prefix18 block19 ⟨state18, 285, 608⟩ ⟨state19, 18, 32⟩ prefix_checked18 checked19
def block20 : List Dir := [.east, .east, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .northWest, .south, .south, .south, .southEast, .southWest, .north, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest]
def state20 : State := {player := 137, boulders := [111, 141, 315, 321], holes := [48, 49]}
theorem checked20 : run soko1_1.board state19 block20 = some ⟨state20, 23, 32⟩ := by decide +kernel
def prefix20 : List Dir := prefix19 ++ block20
theorem prefix_checked20 : run soko1_1.board soko1_1.initial prefix20 = some ⟨state20, 326, 672⟩ :=
  run_append_of _ _ prefix19 block20 ⟨state19, 303, 640⟩ ⟨state20, 23, 32⟩ prefix_checked19 checked20
def block21 : List Dir := [.north, .north, .north, .northWest, .east, .south, .south, .southEast, .east, .east, .east, .southEast, .west, .west, .west, .northWest, .south, .south, .south, .southEast, .west, .west, .west, .northWest, .south, .south, .south, .southEast, .southWest, .north, .north, .north]
def state21 : State := {player := 239, boulders := [213, 315, 321], holes := [49]}
theorem checked21 : run soko1_1.board state20 block21 = some ⟨state21, 19, 32⟩ := by decide +kernel
def prefix21 : List Dir := prefix20 ++ block21
theorem prefix_checked21 : run soko1_1.board soko1_1.initial prefix21 = some ⟨state21, 345, 704⟩ :=
  run_append_of _ _ prefix20 block21 ⟨state20, 326, 672⟩ ⟨state21, 19, 32⟩ prefix_checked20 checked21
def block22 : List Dir := [.north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east]
def state22 : State := {player := 33, boulders := [315, 321], holes := []}
theorem checked22 : run soko1_1.board state21 block22 = some ⟨state22, 12, 17⟩ := by decide +kernel
def prefix22 : List Dir := prefix21 ++ block22
theorem prefix_checked22 : run soko1_1.board soko1_1.initial prefix22 = some ⟨state22, 357, 721⟩ :=
  run_append_of _ _ prefix21 block22 ⟨state21, 345, 704⟩ ⟨state22, 12, 17⟩ prefix_checked21 checked22
def path : List Dir := prefix22
def finalState : State := state22
theorem solution : Trace soko1_1.board soko1_1.initial path finalState 357 721 ∧ Goal finalState :=
  ⟨run_sound _ _ _ _ prefix_checked22, rfl⟩
#print axioms solution
end Owner1007.Witness11
