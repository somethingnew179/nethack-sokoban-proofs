/- Complete real soko4-2 92/319 cost witness.
Untrusted proposer SHA256 1cc7adad3750c094bcb48937b39ac85acc2e4c339231485c93fe46357525e594.
Each16-action block is checked by ordinary decide, then exact run append.
No moves-optimality or solver-reduction assumption occurs here. -/
import NetHack.Sokoban.Maps
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
namespace NetHack.Sokoban.Movement.Paths92x319

def block0 : List Dir := [.southEast, .southEast, .southEast, .east, .north, .southWest, .northWest, .east, .north, .east, .east, .east, .south, .southEast, .east, .east]
def state16 : State := {player := 72, boulders := [40, 21, 52, 35, 84, 55, 41, 57, 127, 128, 129, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124, 125]}
theorem block0_checked : run soko4_2.board soko4_2.initial block0 =
    some ⟨state16, 6, 16⟩ := by decide
def prefix0 : List Dir := block0
theorem prefix0_checked : run soko4_2.board soko4_2.initial prefix0 = some ⟨state16, 6, 16⟩ := block0_checked

def block1 : List Dir := [.northEast, .northWest, .northWest, .south, .east, .southEast, .southWest, .west, .west, .west, .south, .south, .north, .northEast, .east, .east]
def state32 : State := {player := 72, boulders := [114, 56, 40, 21, 52, 35, 55, 57, 127, 128, 129, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124, 125]}
theorem block1_checked : run soko4_2.board state16 block1 =
    some ⟨state32, 3, 16⟩ := by decide
def prefix1 : List Dir := prefix0 ++ block1
theorem prefix1_checked : run soko4_2.board soko4_2.initial prefix1 =
    some ⟨state32, 9, 32⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix0 block1
    ⟨state16, 6, 16⟩ ⟨state32, 3, 16⟩
    prefix0_checked block1_checked

def block2 : List Dir := [.northEast, .northWest, .west, .south, .west, .south, .southWest, .south, .southEast, .southEast, .southWest, .west, .west, .north, .west, .east]
def state48 : State := {player := 128, boulders := [113, 54, 71, 114, 40, 21, 52, 35, 57, 129, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124]}
theorem block2_checked : run soko4_2.board state32 block2 =
    some ⟨state48, 4, 16⟩ := by decide
def prefix2 : List Dir := prefix1 ++ block2
theorem prefix2_checked : run soko4_2.board soko4_2.initial prefix2 =
    some ⟨state48, 13, 48⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix1 block2
    ⟨state32, 9, 32⟩ ⟨state48, 4, 16⟩
    prefix1_checked block2_checked

def block3 : List Dir := [.southEast, .east, .northEast, .northWest, .northWest, .west, .south, .northEast, .southEast, .west, .east, .southEast, .southWest, .west, .north, .west]
def state64 : State := {player := 128, boulders := [127, 114, 113, 54, 71, 40, 21, 52, 35, 57, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124]}
theorem block3_checked : run soko4_2.board state48 block3 =
    some ⟨state64, 4, 16⟩ := by decide
def prefix3 : List Dir := prefix2 ++ block3
theorem prefix3_checked : run soko4_2.board soko4_2.initial prefix3 =
    some ⟨state64, 17, 64⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix2 block3
    ⟨state48, 13, 48⟩ ⟨state64, 4, 16⟩
    prefix2_checked block3_checked

def block4 : List Dir := [.east, .southEast, .northEast, .northWest, .northWest, .south, .north, .north, .north, .northEast, .northEast, .northWest, .south, .west, .west, .west]
def state80 : State := {player := 37, boulders := [55, 129, 127, 113, 54, 71, 21, 52, 35, 57, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124]}
theorem block4_checked : run soko4_2.board state64 block4 =
    some ⟨state80, 2, 16⟩ := by decide
def prefix4 : List Dir := prefix3 ++ block4
theorem prefix4_checked : run soko4_2.board soko4_2.initial prefix4 =
    some ⟨state80, 19, 80⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix3 block4
    ⟨state64, 17, 64⟩ ⟨state80, 2, 16⟩
    prefix3_checked block4_checked

def block5 : List Dir := [.southWest, .southEast, .north, .northWest, .east, .east, .east, .south, .south, .south, .south, .southEast, .southEast, .southWest, .west, .northWest]
def state96 : State := {player := 128, boulders := [114, 40, 55, 129, 127, 113, 71, 21, 35, 57, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124]}
theorem block5_checked : run soko4_2.board state80 block5 =
    some ⟨state96, 8, 16⟩ := by decide
def prefix5 : List Dir := prefix4 ++ block5
theorem prefix5_checked : run soko4_2.board soko4_2.initial prefix5 =
    some ⟨state96, 27, 96⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix4 block5
    ⟨state80, 19, 80⟩ ⟨state96, 8, 16⟩
    prefix4_checked block5_checked

def block6 : List Dir := [.west, .east, .southEast, .east, .northEast, .northWest, .northWest, .west, .south, .northEast, .southEast, .west, .east, .southEast, .southWest, .west]
def state112 : State := {player := 144, boulders := [113, 128, 40, 55, 129, 71, 21, 35, 57, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123]}
theorem block6_checked : run soko4_2.board state96 block6 =
    some ⟨state112, 3, 16⟩ := by decide
def prefix6 : List Dir := prefix5 ++ block6
theorem prefix6_checked : run soko4_2.board soko4_2.initial prefix6 =
    some ⟨state112, 30, 112⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix5 block6
    ⟨state96, 27, 96⟩ ⟨state112, 3, 16⟩
    prefix5_checked block6_checked

def block7 : List Dir := [.north, .west, .west, .east, .east, .southEast, .northEast, .northWest, .northWest, .west, .south, .northEast, .southEast, .west, .south, .west]
def state128 : State := {player := 128, boulders := [127, 113, 40, 55, 71, 21, 35, 57, 130], holes := [31, 46, 61, 76, 91, 121, 122]}
theorem block7_checked : run soko4_2.board state112 block7 =
    some ⟨state128, 6, 16⟩ := by decide
def prefix7 : List Dir := prefix6 ++ block7
theorem prefix7_checked : run soko4_2.board soko4_2.initial prefix7 =
    some ⟨state128, 36, 128⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix6 block7
    ⟨state112, 30, 112⟩ ⟨state128, 6, 16⟩
    prefix6_checked block7_checked

def block8 : List Dir := [.west, .east, .northEast, .northWest, .south, .southEast, .west, .west, .east, .east, .northEast, .southEast, .west, .west, .west, .west]
def state144 : State := {player := 127, boulders := [121, 40, 55, 71, 21, 35, 57], holes := [31, 46, 61, 76, 91]}
theorem block8_checked : run soko4_2.board state128 block8 =
    some ⟨state144, 8, 16⟩ := by decide
def prefix8 : List Dir := prefix7 ++ block8
theorem prefix8_checked : run soko4_2.board soko4_2.initial prefix8 =
    some ⟨state144, 44, 144⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix7 block8
    ⟨state128, 36, 128⟩ ⟨state144, 8, 16⟩
    prefix7_checked block8_checked

def block9 : List Dir := [.west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east, .east, .northEast, .north, .northEast]
def state160 : State := {player := 84, boulders := [40, 55, 71, 21, 35, 57], holes := [31, 46, 61, 76]}
theorem block9_checked : run soko4_2.board state144 block9 =
    some ⟨state160, 1, 16⟩ := by decide
def prefix9 : List Dir := prefix8 ++ block9
theorem prefix9_checked : run soko4_2.board soko4_2.initial prefix9 =
    some ⟨state160, 45, 160⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix8 block9
    ⟨state144, 44, 144⟩ ⟨state160, 1, 16⟩
    prefix8_checked block9_checked

def block10 : List Dir := [.north, .north, .north, .east, .northEast, .south, .east, .southEast, .southWest, .west, .west, .east, .east, .northEast, .northWest, .west]
def state176 : State := {player := 41, boulders := [69, 56, 55, 21, 35, 57], holes := [31, 46, 61, 76]}
theorem block10_checked : run soko4_2.board state160 block10 =
    some ⟨state176, 4, 16⟩ := by decide
def prefix10 : List Dir := prefix9 ++ block10
theorem prefix10_checked : run soko4_2.board soko4_2.initial prefix10 =
    some ⟨state176, 49, 176⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix9 block10
    ⟨state160, 45, 160⟩ ⟨state176, 4, 16⟩
    prefix9_checked block10_checked

def block11 : List Dir := [.west, .south, .northEast, .east, .south, .west, .northWest, .southWest, .south, .south, .south, .south, .north, .north, .north, .north]
def state192 : State := {player := 54, boulders := [129, 55, 72, 70, 21, 35], holes := [31, 46, 61, 76]}
theorem block11_checked : run soko4_2.board state176 block11 =
    some ⟨state192, 7, 16⟩ := by decide
def prefix11 : List Dir := prefix10 ++ block11
theorem prefix11_checked : run soko4_2.board soko4_2.initial prefix11 =
    some ⟨state192, 56, 192⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix10 block11
    ⟨state176, 49, 176⟩ ⟨state192, 7, 16⟩
    prefix10_checked block11_checked

def block12 : List Dir := [.northEast, .southEast, .west, .northWest, .south, .south, .south, .south, .southEast, .west, .north, .north, .north, .northEast, .southEast, .west]
def state208 : State := {player := 70, boulders := [69, 113, 129, 72, 21, 35], holes := [31, 46, 61, 76]}
theorem block12_checked : run soko4_2.board state192 block12 =
    some ⟨state208, 7, 16⟩ := by decide
def prefix12 : List Dir := prefix11 ++ block12
theorem prefix12_checked : run soko4_2.board soko4_2.initial prefix12 =
    some ⟨state208, 63, 208⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix11 block12
    ⟨state192, 56, 192⟩ ⟨state208, 7, 16⟩
    prefix11_checked block12_checked

def block13 : List Dir := [.northWest, .south, .east, .east, .northEast, .southEast, .west, .west, .northWest, .southWest, .south, .south, .southEast, .south, .west, .west]
def state224 : State := {player := 128, boulders := [127, 114, 70, 113, 21, 35], holes := [31, 46, 61, 76]}
theorem block13_checked : run soko4_2.board state208 block13 =
    some ⟨state224, 7, 16⟩ := by decide
def prefix13 : List Dir := prefix12 ++ block13
theorem prefix13_checked : run soko4_2.board soko4_2.initial prefix13 =
    some ⟨state224, 70, 224⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix12 block13
    ⟨state208, 63, 208⟩ ⟨state224, 7, 16⟩
    prefix12_checked block13_checked

def block14 : List Dir := [.east, .northEast, .northWest, .west, .south, .northEast, .south, .north, .north, .north, .northEast, .southEast, .west, .northWest, .south, .south]
def state240 : State := {player := 84, boulders := [99, 129, 128, 127, 21, 35], holes := [31, 46, 61, 76]}
theorem block14_checked : run soko4_2.board state224 block14 =
    some ⟨state240, 5, 16⟩ := by decide
def prefix14 : List Dir := prefix13 ++ block14
theorem prefix14_checked : run soko4_2.board soko4_2.initial prefix14 =
    some ⟨state240, 75, 240⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix13 block14
    ⟨state224, 70, 224⟩ ⟨state240, 5, 16⟩
    prefix13_checked block14_checked

def block15 : List Dir := [.south, .southEast, .south, .southWest, .west, .north, .west, .west, .west, .west, .west, .west, .southWest, .north, .east, .east]
def state256 : State := {player := 123, boulders := [113, 114, 129, 21, 35], holes := [31, 46, 61]}
theorem block15_checked : run soko4_2.board state240 block15 =
    some ⟨state256, 4, 16⟩ := by decide
def prefix15 : List Dir := prefix14 ++ block15
theorem prefix15_checked : run soko4_2.board soko4_2.initial prefix15 =
    some ⟨state256, 79, 256⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix14 block15
    ⟨state240, 75, 240⟩ ⟨state256, 4, 16⟩
    prefix14_checked block15_checked

def block16 : List Dir := [.east, .east, .east, .east, .east, .southEast, .northEast, .west, .west, .east, .northEast, .northWest, .south, .southEast, .southWest, .northWest]
def state272 : State := {player := 128, boulders := [129, 127, 113, 21, 35], holes := [31, 46, 61]}
theorem block16_checked : run soko4_2.board state256 block16 =
    some ⟨state272, 3, 16⟩ := by decide
def prefix16 : List Dir := prefix15 ++ block16
theorem prefix16_checked : run soko4_2.board soko4_2.initial prefix16 =
    some ⟨state272, 82, 272⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix15 block16
    ⟨state256, 79, 256⟩ ⟨state272, 3, 16⟩
    prefix15_checked block16_checked

def block17 : List Dir := [.west, .west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east, .east, .east, .southEast]
def state288 : State := {player := 144, boulders := [129, 113, 21, 35], holes := [31, 46]}
theorem block17_checked : run soko4_2.board state272 block17 =
    some ⟨state288, 2, 16⟩ := by decide
def prefix17 : List Dir := prefix16 ++ block17
theorem prefix17_checked : run soko4_2.board soko4_2.initial prefix17 =
    some ⟨state288, 84, 288⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix16 block17
    ⟨state272, 82, 272⟩ ⟨state288, 2, 16⟩
    prefix16_checked block17_checked

def block18 : List Dir := [.northEast, .west, .west, .west, .west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east]
def state304 : State := {player := 126, boulders := [113, 21, 35], holes := [31]}
theorem block18_checked : run soko4_2.board state288 block18 =
    some ⟨state304, 4, 16⟩ := by decide
def prefix18 : List Dir := prefix17 ++ block18
theorem prefix18_checked : run soko4_2.board soko4_2.initial prefix18 =
    some ⟨state304, 88, 304⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix17 block18
    ⟨state288, 84, 288⟩ ⟨state304, 4, 16⟩
    prefix17_checked block18_checked

def block19 : List Dir := [.east, .east, .northEast, .northWest, .south, .southEast, .west, .west, .west, .west, .west, .west, .west, .southWest, .north]
def state319 : State := {player := 121, boulders := [21, 35], holes := []}
theorem block19_checked : run soko4_2.board state304 block19 =
    some ⟨state319, 4, 15⟩ := by decide
def prefix19 : List Dir := prefix18 ++ block19
theorem prefix19_checked : run soko4_2.board soko4_2.initial prefix19 =
    some ⟨state319, 92, 319⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix18 block19
    ⟨state304, 88, 304⟩ ⟨state319, 4, 15⟩
    prefix18_checked block19_checked

def path : List Dir := prefix19
def finalState : State := state319
theorem checked : run soko4_2.board soko4_2.initial path =
    some ⟨finalState, 92, 319⟩ := prefix19_checked
theorem completed : Goal finalState := rfl
theorem trace : Trace soko4_2.board soko4_2.initial path finalState 92 319 :=
  run_sound _ _ _ _ checked
end NetHack.Sokoban.Movement.Paths92x319
