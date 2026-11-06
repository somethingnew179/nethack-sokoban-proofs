/- Complete real soko4-2 85/322 cost witness.
Untrusted proposer SHA256 3ee561637c5694ff5a9da598a1035c6c617bca336c1c2434c9eea6b2def48468.
Each16-action block is checked by ordinary decide, then exact run append.
No moves-optimality or solver-reduction assumption occurs here. -/
import NetHack.Sokoban.Maps
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
namespace NetHack.Sokoban.Movement.Paths85x322

def block0 : List Dir := [.southEast, .southEast, .north, .east, .east, .east, .east, .south, .south, .south, .northEast, .northEast, .west, .east, .southEast, .northEast]
def state16 : State := {player := 58, boulders := [54, 99, 40, 20, 51, 52, 41, 57, 127, 128, 129, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124, 125]}
theorem block0_checked : run soko4_2.board soko4_2.initial block0 =
    some ⟨state16, 7, 16⟩ := by decide
def prefix0 : List Dir := block0
theorem prefix0_checked : run soko4_2.board soko4_2.initial prefix0 = some ⟨state16, 7, 16⟩ := block0_checked

def block1 : List Dir := [.northWest, .northWest, .west, .south, .northEast, .south, .east, .southEast, .southWest, .west, .west, .southWest, .south, .southEast, .southEast, .southWest]
def state32 : State := {player := 145, boulders := [114, 56, 55, 54, 20, 51, 52, 57, 127, 128, 129, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124, 125]}
theorem block1_checked : run soko4_2.board state16 block1 =
    some ⟨state32, 3, 16⟩ := by decide
def prefix1 : List Dir := prefix0 ++ block1
theorem prefix1_checked : run soko4_2.board soko4_2.initial prefix1 =
    some ⟨state32, 10, 32⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix0 block1
    ⟨state16, 7, 16⟩ ⟨state32, 3, 16⟩
    prefix0_checked block1_checked

def block2 : List Dir := [.west, .west, .north, .west, .east, .southEast, .east, .northEast, .northWest, .northWest, .west, .south, .northEast, .southEast, .west, .east]
def state48 : State := {player := 115, boulders := [113, 128, 56, 55, 54, 20, 51, 52, 57, 129, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124]}
theorem block2_checked : run soko4_2.board state32 block2 =
    some ⟨state48, 4, 16⟩ := by decide
def prefix2 : List Dir := prefix1 ++ block2
theorem prefix2_checked : run soko4_2.board soko4_2.initial prefix2 =
    some ⟨state48, 14, 48⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix1 block2
    ⟨state32, 10, 32⟩ ⟨state48, 4, 16⟩
    prefix1_checked block2_checked

def block3 : List Dir := [.southEast, .southWest, .west, .north, .west, .east, .southEast, .northEast, .west, .southWest, .northWest, .west, .east, .southEast, .northEast, .west]
def state64 : State := {player := 129, boulders := [128, 114, 113, 56, 55, 54, 20, 51, 52, 57], holes := [31, 46, 61, 76, 91, 121, 122, 123]}
theorem block3_checked : run soko4_2.board state48 block3 =
    some ⟨state64, 5, 16⟩ := by decide
def prefix3 : List Dir := prefix2 ++ block3
theorem prefix3_checked : run soko4_2.board soko4_2.initial prefix3 =
    some ⟨state64, 19, 64⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix2 block3
    ⟨state48, 14, 48⟩ ⟨state64, 5, 16⟩
    prefix2_checked block3_checked

def block4 : List Dir := [.west, .east, .northEast, .northWest, .south, .north, .north, .northEast, .east, .east, .northEast, .northWest, .west, .west, .west, .west]
def state80 : State := {player := 38, boulders := [129, 127, 113, 56, 55, 54, 20, 51, 52, 57], holes := [31, 46, 61, 76, 91, 121, 122, 123]}
theorem block4_checked : run soko4_2.board state64 block4 =
    some ⟨state80, 2, 16⟩ := by decide
def prefix4 : List Dir := prefix3 ++ block4
theorem prefix4_checked : run soko4_2.board soko4_2.initial prefix4 =
    some ⟨state80, 21, 80⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix3 block4
    ⟨state64, 19, 64⟩ ⟨state80, 2, 16⟩
    prefix3_checked block4_checked

def block5 : List Dir := [.west, .west, .southWest, .southEast, .east, .north, .southWest, .northWest, .northEast, .east, .east, .east, .south, .south, .east, .east]
def state96 : State := {player := 71, boulders := [84, 40, 129, 127, 113, 56, 55, 20, 51, 57], holes := [31, 46, 61, 76, 91, 121, 122, 123]}
theorem block5_checked : run soko4_2.board state80 block5 =
    some ⟨state96, 6, 16⟩ := by decide
def prefix5 : List Dir := prefix4 ++ block5
theorem prefix5_checked : run soko4_2.board soko4_2.initial prefix5 =
    some ⟨state96, 27, 96⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix4 block5
    ⟨state80, 21, 80⟩ ⟨state96, 6, 16⟩
    prefix4_checked block5_checked

def block6 : List Dir := [.east, .northEast, .northWest, .west, .south, .west, .southWest, .south, .south, .southEast, .south, .southWest, .northWest, .west, .east, .southEast]
def state112 : State := {player := 144, boulders := [114, 54, 71, 40, 129, 113, 20, 51, 57], holes := [31, 46, 61, 76, 91, 121, 122]}
theorem block6_checked : run soko4_2.board state96 block6 =
    some ⟨state112, 5, 16⟩ := by decide
def prefix6 : List Dir := prefix5 ++ block6
theorem prefix6_checked : run soko4_2.board soko4_2.initial prefix6 =
    some ⟨state112, 32, 112⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix5 block6
    ⟨state96, 27, 96⟩ ⟨state112, 5, 16⟩
    prefix5_checked block6_checked

def block7 : List Dir := [.northEast, .west, .west, .west, .east, .east, .northEast, .northWest, .south, .north, .north, .north, .northEast, .northEast, .northWest, .south]
def state128 : State := {player := 40, boulders := [55, 129, 54, 71, 113, 20, 51, 57], holes := [31, 46, 61, 76, 91, 121]}
theorem block7_checked : run soko4_2.board state112 block7 =
    some ⟨state128, 5, 16⟩ := by decide
def prefix7 : List Dir := prefix6 ++ block7
theorem prefix7_checked : run soko4_2.board soko4_2.initial prefix7 =
    some ⟨state128, 37, 128⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix6 block7
    ⟨state112, 32, 112⟩ ⟨state128, 5, 16⟩
    prefix6_checked block7_checked

def block8 : List Dir := [.west, .south, .northEast, .east, .east, .southEast, .west, .northWest, .west, .southWest, .south, .north, .northEast, .east, .southEast, .south]
def state144 : State := {player := 72, boulders := [84, 56, 55, 129, 71, 113, 20, 51], holes := [31, 46, 61, 76, 91, 121]}
theorem block8_checked : run soko4_2.board state128 block8 =
    some ⟨state144, 3, 16⟩ := by decide
def prefix8 : List Dir := prefix7 ++ block8
theorem prefix8_checked : run soko4_2.board soko4_2.initial prefix8 =
    some ⟨state144, 40, 144⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix7 block8
    ⟨state128, 37, 128⟩ ⟨state144, 3, 16⟩
    prefix7_checked block8_checked

def block9 : List Dir := [.west, .northEast, .northWest, .west, .southWest, .south, .south, .south, .southEast, .south, .west, .west, .east, .northEast, .northWest, .south]
def state160 : State := {player := 114, boulders := [129, 127, 70, 56, 55, 113, 20, 51], holes := [31, 46, 61, 76, 91, 121]}
theorem block9_checked : run soko4_2.board state144 block9 =
    some ⟨state160, 6, 16⟩ := by decide
def prefix9 : List Dir := prefix8 ++ block9
theorem prefix9_checked : run soko4_2.board soko4_2.initial prefix9 =
    some ⟨state160, 46, 160⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix8 block9
    ⟨state144, 40, 144⟩ ⟨state160, 6, 16⟩
    prefix8_checked block9_checked

def block10 : List Dir := [.north, .north, .north, .north, .northEast, .east, .southEast, .southWest, .west, .east, .northEast, .northWest, .west, .south, .northEast, .southEast]
def state176 : State := {player := 57, boulders := [70, 69, 129, 127, 56, 113, 20, 51], holes := [31, 46, 61, 76, 91, 121]}
theorem block10_checked : run soko4_2.board state160 block10 =
    some ⟨state176, 2, 16⟩ := by decide
def prefix10 : List Dir := prefix9 ++ block10
theorem prefix10_checked : run soko4_2.board soko4_2.initial prefix10 =
    some ⟨state176, 48, 176⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix9 block10
    ⟨state160, 46, 160⟩ ⟨state176, 2, 16⟩
    prefix9_checked block10_checked

def block11 : List Dir := [.west, .northWest, .southWest, .south, .south, .south, .southEast, .south, .southWest, .northWest, .west, .east, .southEast, .northEast, .west, .west]
def state192 : State := {player := 128, boulders := [127, 114, 55, 70, 113, 20, 51], holes := [31, 46, 61, 76, 91]}
theorem block11_checked : run soko4_2.board state176 block11 =
    some ⟨state192, 7, 16⟩ := by decide
def prefix11 : List Dir := prefix10 ++ block11
theorem prefix11_checked : run soko4_2.board soko4_2.initial prefix11 =
    some ⟨state192, 55, 192⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix10 block11
    ⟨state176, 48, 176⟩ ⟨state192, 7, 16⟩
    prefix10_checked block11_checked

def block12 : List Dir := [.east, .northEast, .northWest, .south, .north, .north, .north, .north, .northEast, .southEast, .west, .northWest, .south, .south, .south, .south]
def state208 : State := {player := 99, boulders := [114, 129, 127, 70, 113, 20, 51], holes := [31, 46, 61, 76, 91]}
theorem block12_checked : run soko4_2.board state192 block12 =
    some ⟨state208, 6, 16⟩ := by decide
def prefix12 : List Dir := prefix11 ++ block12
theorem prefix12_checked : run soko4_2.board soko4_2.initial prefix12 =
    some ⟨state208, 61, 208⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix11 block12
    ⟨state192, 55, 192⟩ ⟨state208, 6, 16⟩
    prefix11_checked block12_checked

def block13 : List Dir := [.southEast, .south, .southWest, .northWest, .west, .west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east]
def state224 : State := {player := 125, boulders := [114, 129, 70, 113, 20, 51], holes := [31, 46, 61, 76]}
theorem block13_checked : run soko4_2.board state208 block13 =
    some ⟨state224, 2, 16⟩ := by decide
def prefix13 : List Dir := prefix12 ++ block13
theorem prefix13_checked : run soko4_2.board soko4_2.initial prefix13 =
    some ⟨state224, 63, 224⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix12 block13
    ⟨state208, 61, 208⟩ ⟨state224, 2, 16⟩
    prefix12_checked block13_checked

def block14 : List Dir := [.east, .east, .east, .southEast, .northEast, .west, .west, .east, .northEast, .northWest, .south, .north, .north, .north, .northEast, .southEast]
def state240 : State := {player := 71, boulders := [129, 127, 70, 113, 20, 51], holes := [31, 46, 61, 76]}
theorem block14_checked : run soko4_2.board state224 block14 =
    some ⟨state240, 3, 16⟩ := by decide
def prefix14 : List Dir := prefix13 ++ block14
theorem prefix14_checked : run soko4_2.board soko4_2.initial prefix14 =
    some ⟨state240, 66, 240⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix13 block14
    ⟨state224, 63, 224⟩ ⟨state240, 3, 16⟩
    prefix13_checked block14_checked

def block15 : List Dir := [.west, .northWest, .south, .south, .south, .southEast, .south, .southWest, .northWest, .west, .west, .west, .west, .west, .west, .southWest]
def state256 : State := {player := 136, boulders := [121, 114, 129, 113, 20, 51], holes := [31, 46, 61, 76]}
theorem block15_checked : run soko4_2.board state240 block15 =
    some ⟨state256, 5, 16⟩ := by decide
def prefix15 : List Dir := prefix14 ++ block15
theorem prefix15_checked : run soko4_2.board soko4_2.initial prefix15 =
    some ⟨state256, 71, 256⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix14 block15
    ⟨state240, 66, 240⟩ ⟨state256, 5, 16⟩
    prefix14_checked block15_checked

def block16 : List Dir := [.north, .east, .east, .east, .east, .east, .east, .east, .southEast, .northEast, .west, .west, .east, .northEast, .northWest, .south]
def state272 : State := {player := 114, boulders := [129, 127, 113, 20, 51], holes := [31, 46, 61]}
theorem block16_checked : run soko4_2.board state256 block16 =
    some ⟨state272, 4, 16⟩ := by decide
def prefix16 : List Dir := prefix15 ++ block16
theorem prefix16_checked : run soko4_2.board soko4_2.initial prefix16 =
    some ⟨state272, 75, 272⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix15 block16
    ⟨state256, 71, 256⟩ ⟨state272, 4, 16⟩
    prefix15_checked block16_checked

def block17 : List Dir := [.southEast, .southWest, .northWest, .west, .west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east]
def state288 : State := {player := 126, boulders := [129, 113, 20, 51], holes := [31, 46]}
theorem block17_checked : run soko4_2.board state272 block17 =
    some ⟨state288, 2, 16⟩ := by decide
def prefix17 : List Dir := prefix16 ++ block17
theorem prefix17_checked : run soko4_2.board soko4_2.initial prefix17 =
    some ⟨state288, 77, 288⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix16 block17
    ⟨state272, 75, 272⟩ ⟨state288, 2, 16⟩
    prefix16_checked block17_checked

def block18 : List Dir := [.east, .east, .southEast, .northEast, .west, .west, .west, .west, .west, .west, .west, .west, .southWest, .north, .east, .east]
def state304 : State := {player := 123, boulders := [113, 20, 51], holes := [31]}
theorem block18_checked : run soko4_2.board state288 block18 =
    some ⟨state304, 4, 16⟩ := by decide
def prefix18 : List Dir := prefix17 ++ block18
theorem prefix18_checked : run soko4_2.board soko4_2.initial prefix18 =
    some ⟨state304, 81, 304⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix17 block18
    ⟨state288, 77, 288⟩ ⟨state304, 4, 16⟩
    prefix17_checked block18_checked

def block19 : List Dir := [.east, .east, .east, .east, .east, .northEast, .northWest, .south, .southEast, .west, .west, .west, .west, .west, .west, .west]
def state320 : State := {player := 122, boulders := [121, 20, 51], holes := [31]}
theorem block19_checked : run soko4_2.board state304 block19 =
    some ⟨state320, 3, 16⟩ := by decide
def prefix19 : List Dir := prefix18 ++ block19
theorem prefix19_checked : run soko4_2.board soko4_2.initial prefix19 =
    some ⟨state320, 84, 320⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix18 block19
    ⟨state304, 81, 304⟩ ⟨state320, 3, 16⟩
    prefix18_checked block19_checked

def block20 : List Dir := [.southWest, .north]
def state322 : State := {player := 121, boulders := [20, 51], holes := []}
theorem block20_checked : run soko4_2.board state320 block20 =
    some ⟨state322, 1, 2⟩ := by decide
def prefix20 : List Dir := prefix19 ++ block20
theorem prefix20_checked : run soko4_2.board soko4_2.initial prefix20 =
    some ⟨state322, 85, 322⟩ :=
  run_append_of soko4_2.board soko4_2.initial prefix19 block20
    ⟨state320, 84, 320⟩ ⟨state322, 1, 2⟩
    prefix19_checked block20_checked

def path : List Dir := prefix20
def finalState : State := state322
theorem checked : run soko4_2.board soko4_2.initial path =
    some ⟨finalState, 85, 322⟩ := prefix20_checked
theorem completed : Goal finalState := rfl
theorem trace : Trace soko4_2.board soko4_2.initial path finalState 85 322 :=
  run_sound _ _ _ _ checked
end NetHack.Sokoban.Movement.Paths85x322
