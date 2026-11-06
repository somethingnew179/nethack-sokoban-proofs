/- Complete real soko2-1 proposed path. All blocks are checked by the
Lean kernel; the C++ solver and its search/pruning claims are not trusted.
This establishes an upper bound, with no initial-state optimality claim. -/
import NetHack.Sokoban.Maps

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace NetHack.Sokoban.Generated

def soko2_1CandidateBlock0 : List Dir := [.west, .northWest, .west, .north, .north, .north, .north, .northWest, .north, .northWest, .northEast, .south, .south, .north, .northEast, .southEast, .west, .northWest, .southWest, .southEast, .south, .south, .southEast, .south, .south, .south, .southWest, .northWest, .east, .east, .north, .north]
def soko2_1CandidateState32 : State := {player := 143, boulders := [184, 122, 42, 65, 67, 47, 48, 70, 71, 142, 162, 145, 126], holes := [188, 189, 190, 191, 192, 193, 194, 195, 196, 197]}
theorem soko2_1Candidate_block0_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidateBlock0 = some ⟨soko2_1CandidateState32, 8, 32⟩ := by decide

def soko2_1CandidatePrefix0 : List Dir := soko2_1CandidateBlock0
theorem soko2_1Candidate_prefix0_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix0 =
      some ⟨soko2_1CandidateState32, 8, 32⟩ := soko2_1Candidate_block0_checked

def soko2_1CandidateBlock1 : List Dir := [.north, .northWest, .southWest, .south, .east, .south, .southEast, .east, .east, .east, .west, .west, .west, .southWest, .northWest, .east, .north, .north, .northWest, .northEast, .southEast, .south, .west, .northWest, .east, .north, .north, .north, .northWest, .northEast, .south, .south]
def soko2_1CandidateState64 : State := {player := 62, boulders := [82, 123, 163, 183, 65, 67, 47, 48, 70, 71, 145, 126], holes := [189, 190, 191, 192, 193, 194, 195, 196, 197]}
theorem soko2_1Candidate_block1_checked :
    run soko2_1.board soko2_1CandidateState32 soko2_1CandidateBlock1 = some ⟨soko2_1CandidateState64, 10, 32⟩ := by decide

def soko2_1CandidatePrefix1 : List Dir := soko2_1CandidatePrefix0 ++ soko2_1CandidateBlock1
theorem soko2_1Candidate_prefix1_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix1 =
      some ⟨soko2_1CandidateState64, 18, 64⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix0 soko2_1CandidateBlock1
    ⟨soko2_1CandidateState32, 8, 32⟩ ⟨soko2_1CandidateState64, 10, 32⟩
    soko2_1Candidate_prefix0_checked soko2_1Candidate_block1_checked

def soko2_1CandidateBlock2 : List Dir := [.south, .south, .southWest, .south, .southEast, .south, .east, .east, .east, .east, .west, .west, .west, .northWest, .northEast, .south, .northWest, .northWest, .northEast, .east, .south, .south, .west, .northWest, .east, .south, .south, .south, .east, .east, .east, .east]
def soko2_1CandidateState96 : State := {player := 186, boulders := [123, 163, 65, 67, 47, 48, 70, 71, 145, 126], holes := [191, 192, 193, 194, 195, 196, 197]}
theorem soko2_1Candidate_block2_checked :
    run soko2_1.board soko2_1CandidateState64 soko2_1CandidateBlock2 = some ⟨soko2_1CandidateState96, 14, 32⟩ := by decide

def soko2_1CandidatePrefix2 : List Dir := soko2_1CandidatePrefix1 ++ soko2_1CandidateBlock2
theorem soko2_1Candidate_prefix2_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix2 =
      some ⟨soko2_1CandidateState96, 32, 96⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix1 soko2_1CandidateBlock2
    ⟨soko2_1CandidateState64, 18, 64⟩ ⟨soko2_1CandidateState96, 14, 32⟩
    soko2_1Candidate_prefix1_checked soko2_1Candidate_block2_checked

def soko2_1CandidateBlock3 : List Dir := [.west, .west, .west, .northWest, .northEast, .south, .north, .northWest, .northEast, .south, .south, .southWest, .south, .east, .east, .east, .east, .west, .west, .west, .northWest, .northEast, .south, .southWest, .east, .east, .east, .east, .west, .west, .northWest, .north]
def soko2_1CandidateState128 : State := {player := 143, boulders := [65, 67, 47, 48, 70, 71, 145, 126], holes := [193, 194, 195, 196, 197]}
theorem soko2_1Candidate_block3_checked :
    run soko2_1.board soko2_1CandidateState96 soko2_1CandidateBlock3 = some ⟨soko2_1CandidateState128, 12, 32⟩ := by decide

def soko2_1CandidatePrefix3 : List Dir := soko2_1CandidatePrefix2 ++ soko2_1CandidateBlock3
theorem soko2_1Candidate_prefix3_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix3 =
      some ⟨soko2_1CandidateState128, 44, 128⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix2 soko2_1CandidateBlock3
    ⟨soko2_1CandidateState96, 32, 96⟩ ⟨soko2_1CandidateState128, 12, 32⟩
    soko2_1Candidate_prefix2_checked soko2_1Candidate_block3_checked

def soko2_1CandidateBlock4 : List Dir := [.north, .north, .northWest, .north, .northEast, .east, .east, .northEast, .east, .east, .south, .south, .west, .south, .southWest, .south, .west, .south, .northEast, .south, .west, .south, .north, .north, .northEast, .northEast, .north, .northEast, .northWest, .west, .west, .west]
def soko2_1CandidateState160 : State := {player := 24, boulders := [185, 166, 66, 88, 65, 47, 70, 71], holes := [193, 194, 195, 196, 197]}
theorem soko2_1Candidate_block4_checked :
    run soko2_1.board soko2_1CandidateState128 soko2_1CandidateBlock4 = some ⟨soko2_1CandidateState160, 7, 32⟩ := by decide

def soko2_1CandidatePrefix4 : List Dir := soko2_1CandidatePrefix3 ++ soko2_1CandidateBlock4
theorem soko2_1Candidate_prefix4_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix4 =
      some ⟨soko2_1CandidateState160, 51, 160⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix3 soko2_1CandidateBlock4
    ⟨soko2_1CandidateState128, 44, 128⟩ ⟨soko2_1CandidateState160, 7, 32⟩
    soko2_1Candidate_prefix3_checked soko2_1Candidate_block4_checked

def soko2_1CandidateBlock5 : List Dir := [.southWest, .southWest, .south, .south, .south, .south, .southEast, .southEast, .east, .east, .northWest, .northEast, .south, .southWest, .east, .west, .west, .northWest, .north, .north, .north, .northWest, .north, .northEast, .southEast, .southEast, .north, .northWest, .northEast, .east, .east, .southEast]
def soko2_1CandidateState192 : State := {player := 48, boulders := [45, 66, 88, 47, 70, 71], holes := [195, 196, 197]}
theorem soko2_1Candidate_block5_checked :
    run soko2_1.board soko2_1CandidateState160 soko2_1CandidateBlock5 = some ⟨soko2_1CandidateState192, 5, 32⟩ := by decide

def soko2_1CandidatePrefix5 : List Dir := soko2_1CandidatePrefix4 ++ soko2_1CandidateBlock5
theorem soko2_1Candidate_prefix5_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix5 =
      some ⟨soko2_1CandidateState192, 56, 192⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix4 soko2_1CandidateBlock5
    ⟨soko2_1CandidateState160, 51, 160⟩ ⟨soko2_1CandidateState192, 5, 32⟩
    soko2_1Candidate_prefix4_checked soko2_1Candidate_block5_checked

def soko2_1CandidateBlock6 : List Dir := [.southWest, .west, .west, .southWest, .north, .east, .east, .east, .northEast, .northWest, .west, .west, .south, .west, .west, .northWest, .south, .south, .northEast, .east, .east, .northEast, .east, .southEast, .southWest, .west, .west, .north, .northEast, .east, .south, .northWest]
def soko2_1CandidateState224 : State := {player := 26, boulders := [67, 64, 82, 88, 70, 71], holes := [195, 196, 197]}
theorem soko2_1Candidate_block6_checked :
    run soko2_1.board soko2_1CandidateState192 soko2_1CandidateBlock6 = some ⟨soko2_1CandidateState224, 10, 32⟩ := by decide

def soko2_1CandidatePrefix6 : List Dir := soko2_1CandidatePrefix5 ++ soko2_1CandidateBlock6
theorem soko2_1Candidate_prefix6_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix6 =
      some ⟨soko2_1CandidateState224, 66, 224⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix5 soko2_1CandidateBlock6
    ⟨soko2_1CandidateState192, 56, 192⟩ ⟨soko2_1CandidateState224, 10, 32⟩
    soko2_1Candidate_prefix5_checked soko2_1Candidate_block6_checked

def soko2_1CandidateBlock7 : List Dir := [.southWest, .south, .southWest, .north, .northEast, .west, .west, .east, .east, .northEast, .southEast, .southEast, .west, .west, .west, .southWest, .north, .northEast, .west, .northWest, .west, .southWest, .southEast, .south, .south, .north, .north, .northWest, .northEast, .south, .south, .north]
def soko2_1CandidateState256 : State := {player := 42, boulders := [82, 122, 43, 88, 70, 71], holes := [195, 196, 197]}
theorem soko2_1Candidate_block7_checked :
    run soko2_1.board soko2_1CandidateState224 soko2_1CandidateBlock7 = some ⟨soko2_1CandidateState256, 12, 32⟩ := by decide

def soko2_1CandidatePrefix7 : List Dir := soko2_1CandidatePrefix6 ++ soko2_1CandidateBlock7
theorem soko2_1Candidate_prefix7_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix7 =
      some ⟨soko2_1CandidateState256, 78, 256⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix6 soko2_1CandidateBlock7
    ⟨soko2_1CandidateState224, 66, 224⟩ ⟨soko2_1CandidateState256, 12, 32⟩
    soko2_1Candidate_prefix6_checked soko2_1Candidate_block7_checked

def soko2_1CandidateBlock8 : List Dir := [.northEast, .southEast, .west, .northWest, .southWest, .southEast, .south, .north, .northWest, .northEast, .east, .east, .southEast, .southEast, .southEast, .south, .south, .southWest, .southWest, .southWest, .northWest, .northWest, .northWest, .east, .south, .southEast, .southEast, .northEast, .north, .north, .northEast, .northEast]
def soko2_1CandidateState288 : State := {player := 87, boulders := [123, 102, 42, 88, 70, 71], holes := [195, 196, 197]}
theorem soko2_1Candidate_block8_checked :
    run soko2_1.board soko2_1CandidateState256 soko2_1CandidateBlock8 = some ⟨soko2_1CandidateState288, 3, 32⟩ := by decide

def soko2_1CandidatePrefix8 : List Dir := soko2_1CandidatePrefix7 ++ soko2_1CandidateBlock8
theorem soko2_1Candidate_prefix8_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix8 =
      some ⟨soko2_1CandidateState288, 81, 288⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix7 soko2_1CandidateBlock8
    ⟨soko2_1CandidateState256, 78, 256⟩ ⟨soko2_1CandidateState288, 3, 32⟩
    soko2_1Candidate_prefix7_checked soko2_1Candidate_block8_checked

def soko2_1CandidateBlock9 : List Dir := [.northWest, .west, .west, .northWest, .northWest, .southWest, .south, .southEast, .south, .north, .north, .northWest, .northEast, .south, .south, .northEast, .east, .east, .southEast, .southEast, .south, .south, .southWest, .southWest, .southWest, .northWest, .northWest, .northWest, .northEast, .south, .northEast, .south]
def soko2_1CandidateState320 : State := {player := 123, boulders := [143, 142, 82, 88, 70, 71], holes := [195, 196, 197]}
theorem soko2_1Candidate_block9_checked :
    run soko2_1.board soko2_1CandidateState288 soko2_1CandidateBlock9 = some ⟨soko2_1CandidateState320, 5, 32⟩ := by decide

def soko2_1CandidatePrefix9 : List Dir := soko2_1CandidatePrefix8 ++ soko2_1CandidateBlock9
theorem soko2_1Candidate_prefix9_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix9 =
      some ⟨soko2_1CandidateState320, 86, 320⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix8 soko2_1CandidateBlock9
    ⟨soko2_1CandidateState288, 81, 288⟩ ⟨soko2_1CandidateState320, 5, 32⟩
    soko2_1Candidate_prefix8_checked soko2_1Candidate_block9_checked

def soko2_1CandidateBlock10 : List Dir := [.west, .south, .south, .east, .southEast, .northEast, .north, .north, .northEast, .northEast, .northWest, .west, .west, .northWest, .southWest, .south, .south, .south, .south, .northEast, .south, .north, .north, .northWest, .north, .northEast, .east, .east, .southEast, .southEast, .south, .south]
def soko2_1CandidateState352 : State := {player := 127, boulders := [163, 162, 182, 88, 70, 71], holes := [195, 196, 197]}
theorem soko2_1Candidate_block10_checked :
    run soko2_1.board soko2_1CandidateState320 soko2_1CandidateBlock10 = some ⟨soko2_1CandidateState352, 7, 32⟩ := by decide

def soko2_1CandidatePrefix10 : List Dir := soko2_1CandidatePrefix9 ++ soko2_1CandidateBlock10
theorem soko2_1Candidate_prefix10_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix10 =
      some ⟨soko2_1CandidateState352, 93, 352⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix9 soko2_1CandidateBlock10
    ⟨soko2_1CandidateState320, 86, 320⟩ ⟨soko2_1CandidateState352, 7, 32⟩
    soko2_1Candidate_prefix9_checked soko2_1Candidate_block10_checked

def soko2_1CandidateBlock11 : List Dir := [.southWest, .southWest, .southWest, .west, .southWest, .northWest, .east, .east, .east, .east, .north, .north, .north, .northEast, .northEast, .northWest, .west, .west, .northWest, .southWest, .south, .south, .south, .south, .south, .north, .north, .north, .north, .north, .northEast, .east]
def soko2_1CandidateState384 : State := {player := 44, boulders := [182, 186, 163, 88, 70, 71], holes := [195, 196, 197]}
theorem soko2_1Candidate_block11_checked :
    run soko2_1.board soko2_1CandidateState352 soko2_1CandidateBlock11 = some ⟨soko2_1CandidateState384, 5, 32⟩ := by decide

def soko2_1CandidatePrefix11 : List Dir := soko2_1CandidatePrefix10 ++ soko2_1CandidateBlock11
theorem soko2_1Candidate_prefix11_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix11 =
      some ⟨soko2_1CandidateState384, 98, 384⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix10 soko2_1CandidateBlock11
    ⟨soko2_1CandidateState352, 93, 352⟩ ⟨soko2_1CandidateState384, 5, 32⟩
    soko2_1Candidate_prefix10_checked soko2_1Candidate_block11_checked

def soko2_1CandidateBlock12 : List Dir := [.east, .southEast, .southEast, .south, .south, .southWest, .southWest, .southWest, .west, .southWest, .northWest, .east, .east, .northWest, .north, .north, .north, .north, .north, .northEast, .east, .east, .southEast, .southEast, .south, .south, .southWest, .south, .southWest, .east, .north, .north]
def soko2_1CandidateState416 : State := {player := 146, boulders := [184, 163, 88, 70, 71], holes := [196, 197]}
theorem soko2_1Candidate_block12_checked :
    run soko2_1.board soko2_1CandidateState384 soko2_1CandidateBlock12 = some ⟨soko2_1CandidateState416, 3, 32⟩ := by decide

def soko2_1CandidatePrefix12 : List Dir := soko2_1CandidatePrefix11 ++ soko2_1CandidateBlock12
theorem soko2_1Candidate_prefix12_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix12 =
      some ⟨soko2_1CandidateState416, 101, 416⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix11 soko2_1CandidateBlock12
    ⟨soko2_1CandidateState384, 98, 384⟩ ⟨soko2_1CandidateState416, 3, 32⟩
    soko2_1Candidate_prefix11_checked soko2_1Candidate_block12_checked

def soko2_1CandidateBlock13 : List Dir := [.north, .north, .northEast, .northWest, .west, .west, .northWest, .southWest, .south, .south, .south, .south, .south, .southEast, .east, .east, .west, .west, .northWest, .northEast, .south, .southWest, .east, .north, .north, .north, .north, .northWest, .north, .northEast, .east, .east]
def soko2_1CandidateState448 : State := {player := 45, boulders := [184, 186, 88, 70, 71], holes := [196, 197]}
theorem soko2_1Candidate_block13_checked :
    run soko2_1.board soko2_1CandidateState416 soko2_1CandidateBlock13 = some ⟨soko2_1CandidateState448, 4, 32⟩ := by decide

def soko2_1CandidatePrefix13 : List Dir := soko2_1CandidatePrefix12 ++ soko2_1CandidateBlock13
theorem soko2_1Candidate_prefix13_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix13 =
      some ⟨soko2_1CandidateState448, 105, 448⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix12 soko2_1CandidateBlock13
    ⟨soko2_1CandidateState416, 101, 416⟩ ⟨soko2_1CandidateState448, 4, 32⟩
    soko2_1Candidate_prefix12_checked soko2_1Candidate_block13_checked

def soko2_1CandidateBlock14 : List Dir := [.southEast, .southEast, .south, .south, .southWest, .south, .southWest, .east, .north, .north, .north, .north, .northEast, .northWest, .west, .west, .northWest, .southWest, .south, .south, .south, .south, .south, .southEast, .east, .east, .east]
def soko2_1CandidateState475 : State := {player := 186, boulders := [88, 70, 71], holes := []}
theorem soko2_1Candidate_block14_checked :
    run soko2_1.board soko2_1CandidateState448 soko2_1CandidateBlock14 = some ⟨soko2_1CandidateState475, 4, 27⟩ := by decide

def soko2_1CandidatePrefix14 : List Dir := soko2_1CandidatePrefix13 ++ soko2_1CandidateBlock14
theorem soko2_1Candidate_prefix14_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePrefix14 =
      some ⟨soko2_1CandidateState475, 109, 475⟩ :=
  run_append_of soko2_1.board soko2_1.initial soko2_1CandidatePrefix13 soko2_1CandidateBlock14
    ⟨soko2_1CandidateState448, 105, 448⟩ ⟨soko2_1CandidateState475, 4, 27⟩
    soko2_1Candidate_prefix13_checked soko2_1Candidate_block14_checked

def soko2_1CandidatePath : List Dir := soko2_1CandidatePrefix14
def soko2_1CandidateFinalState : State := soko2_1CandidateState475

theorem soko2_1_candidate_checked :
    run soko2_1.board soko2_1.initial soko2_1CandidatePath =
      some ⟨soko2_1CandidateFinalState, 109, 475⟩ := soko2_1Candidate_prefix14_checked

theorem soko2_1_candidate_goal : Goal soko2_1CandidateFinalState := by rfl

theorem soko2_1_candidate_trace :
    Trace soko2_1.board soko2_1.initial soko2_1CandidatePath soko2_1CandidateFinalState 109 475 :=
  run_sound _ _ _ _ soko2_1_candidate_checked

end NetHack.Sokoban.Generated
