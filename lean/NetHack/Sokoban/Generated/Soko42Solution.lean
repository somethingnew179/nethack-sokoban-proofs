/- Complete real soko4-2 proposed path. All blocks are checked by the
Lean kernel; the C++ solver and its search/pruning claims are not trusted.
This establishes an upper bound, with no initial-state optimality claim. -/
import NetHack.Sokoban.Maps

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace NetHack.Sokoban.Generated

def soko4_2CandidateBlock0 : List Dir := [.east, .east, .south, .east, .east, .east, .east, .south, .south, .south, .northEast, .northEast, .west, .east, .southEast, .northEast, .northWest, .northWest, .west, .south, .northEast, .southEast, .southEast, .west, .southWest, .west, .southWest, .south, .southEast, .southEast, .southWest, .west]
def soko4_2CandidateState32 : State := {player := 144, boulders := [114, 56, 55, 54, 50, 51, 52, 41, 127, 128, 129, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123, 124, 125]}
theorem soko4_2Candidate_block0_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidateBlock0 = some ⟨soko4_2CandidateState32, 10, 32⟩ := by decide

def soko4_2CandidatePrefix0 : List Dir := soko4_2CandidateBlock0
theorem soko4_2Candidate_prefix0_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix0 =
      some ⟨soko4_2CandidateState32, 10, 32⟩ := soko4_2Candidate_block0_checked

def soko4_2CandidateBlock1 : List Dir := [.west, .north, .west, .east, .southEast, .east, .northEast, .northWest, .northWest, .west, .south, .northEast, .southEast, .west, .east, .southEast, .southWest, .west, .north, .west, .west, .east, .east, .southEast, .northEast, .northWest, .northWest, .west, .south, .northEast, .southEast, .southEast]
def soko4_2CandidateState64 : State := {player := 131, boulders := [128, 114, 56, 55, 54, 50, 51, 52, 41, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123]}
theorem soko4_2Candidate_block1_checked :
    run soko4_2.board soko4_2CandidateState32 soko4_2CandidateBlock1 = some ⟨soko4_2CandidateState64, 8, 32⟩ := by decide

def soko4_2CandidatePrefix1 : List Dir := soko4_2CandidatePrefix0 ++ soko4_2CandidateBlock1
theorem soko4_2Candidate_prefix1_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix1 =
      some ⟨soko4_2CandidateState64, 18, 64⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix0 soko4_2CandidateBlock1
    ⟨soko4_2CandidateState32, 10, 32⟩ ⟨soko4_2CandidateState64, 8, 32⟩
    soko4_2Candidate_prefix0_checked soko4_2Candidate_block1_checked

def soko4_2CandidateBlock2 : List Dir := [.southWest, .northWest, .west, .north, .northEast, .southEast, .west, .north, .north, .northEast, .east, .northEast, .north, .northWest, .west, .southWest, .south, .northEast, .south, .north, .northEast, .southEast, .west, .northWest, .south, .southWest, .south, .south, .south, .southEast, .southEast, .southWest]
def soko4_2CandidateState96 : State := {player := 145, boulders := [114, 55, 70, 113, 127, 56, 50, 51, 52, 130], holes := [31, 46, 61, 76, 91, 121, 122, 123]}
theorem soko4_2Candidate_block2_checked :
    run soko4_2.board soko4_2CandidateState64 soko4_2CandidateBlock2 = some ⟨soko4_2CandidateState96, 9, 32⟩ := by decide

def soko4_2CandidatePrefix2 : List Dir := soko4_2CandidatePrefix1 ++ soko4_2CandidateBlock2
theorem soko4_2Candidate_prefix2_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix2 =
      some ⟨soko4_2CandidateState96, 27, 96⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix1 soko4_2CandidateBlock2
    ⟨soko4_2CandidateState64, 18, 64⟩ ⟨soko4_2CandidateState96, 9, 32⟩
    soko4_2Candidate_prefix1_checked soko4_2Candidate_block2_checked

def soko4_2CandidateBlock3 : List Dir := [.west, .northWest, .west, .east, .east, .southEast, .northEast, .northWest, .northWest, .west, .south, .northEast, .southEast, .west, .north, .north, .north, .north, .northEast, .east, .southEast, .southWest, .west, .east, .northEast, .northWest, .west, .west, .west, .west, .west, .west]
def soko4_2CandidateState128 : State := {player := 35, boulders := [69, 113, 128, 55, 56, 50, 51, 52, 130], holes := [31, 46, 61, 76, 91, 121, 122]}
theorem soko4_2Candidate_block3_checked :
    run soko4_2.board soko4_2CandidateState96 soko4_2CandidateBlock3 = some ⟨soko4_2CandidateState128, 4, 32⟩ := by decide

def soko4_2CandidatePrefix3 : List Dir := soko4_2CandidatePrefix2 ++ soko4_2CandidateBlock3
theorem soko4_2Candidate_prefix3_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix3 =
      some ⟨soko4_2CandidateState128, 31, 128⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix2 soko4_2CandidateBlock3
    ⟨soko4_2CandidateState96, 27, 96⟩ ⟨soko4_2CandidateState128, 4, 32⟩
    soko4_2Candidate_prefix2_checked soko4_2Candidate_block3_checked

def soko4_2CandidateBlock4 : List Dir := [.southWest, .southEast, .east, .east, .north, .southWest, .west, .northWest, .northEast, .east, .east, .east, .east, .south, .south, .east, .east, .northEast, .northWest, .south, .west, .southWest, .south, .south, .southEast, .southEast, .southWest, .northWest, .west, .east, .southEast, .northEast]
def soko4_2CandidateState160 : State := {player := 131, boulders := [127, 114, 54, 71, 40, 113, 50, 51, 130], holes := [31, 46, 61, 76, 91, 121, 122]}
theorem soko4_2Candidate_block4_checked :
    run soko4_2.board soko4_2CandidateState128 soko4_2CandidateBlock4 = some ⟨soko4_2CandidateState160, 10, 32⟩ := by decide

def soko4_2CandidatePrefix4 : List Dir := soko4_2CandidatePrefix3 ++ soko4_2CandidateBlock4
theorem soko4_2Candidate_prefix4_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix4 =
      some ⟨soko4_2CandidateState160, 41, 160⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix3 soko4_2CandidateBlock4
    ⟨soko4_2CandidateState128, 31, 128⟩ ⟨soko4_2CandidateState160, 10, 32⟩
    soko4_2Candidate_prefix3_checked soko4_2Candidate_block4_checked

def soko4_2CandidateBlock5 : List Dir := [.west, .southWest, .northWest, .west, .east, .southEast, .northEast, .west, .west, .west, .east, .east, .northEast, .northWest, .west, .south, .northEast, .southEast, .west, .north, .north, .north, .northEast, .northEast, .northWest, .south, .west, .south, .south, .north, .northEast, .southEast]
def soko4_2CandidateState192 : State := {player := 56, boulders := [84, 55, 113, 128, 71, 50, 51], holes := [31, 46, 61, 76, 91]}
theorem soko4_2Candidate_block5_checked :
    run soko4_2.board soko4_2CandidateState160 soko4_2CandidateBlock5 = some ⟨soko4_2CandidateState192, 10, 32⟩ := by decide

def soko4_2CandidatePrefix5 : List Dir := soko4_2CandidatePrefix4 ++ soko4_2CandidateBlock5
theorem soko4_2Candidate_prefix5_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix5 =
      some ⟨soko4_2CandidateState192, 51, 192⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix4 soko4_2CandidateBlock5
    ⟨soko4_2CandidateState160, 41, 160⟩ ⟨soko4_2CandidateState192, 10, 32⟩
    soko4_2Candidate_prefix4_checked soko4_2Candidate_block5_checked

def soko4_2CandidateBlock6 : List Dir := [.west, .southWest, .south, .south, .southEast, .southWest, .west, .east, .northEast, .northWest, .south, .north, .north, .north, .northEast, .northWest, .south, .south, .east, .northEast, .southEast, .west, .northWest, .southWest, .south, .south, .southEast, .south, .southWest, .northWest, .west, .west]
def soko4_2CandidateState224 : State := {player := 126, boulders := [121, 114, 70, 129, 113, 50, 51], holes := [31, 46, 61, 76, 91]}
theorem soko4_2Candidate_block6_checked :
    run soko4_2.board soko4_2CandidateState192 soko4_2CandidateBlock6 = some ⟨soko4_2CandidateState224, 11, 32⟩ := by decide

def soko4_2CandidatePrefix6 : List Dir := soko4_2CandidatePrefix5 ++ soko4_2CandidateBlock6
theorem soko4_2Candidate_prefix6_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix6 =
      some ⟨soko4_2CandidateState224, 62, 224⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix5 soko4_2CandidateBlock6
    ⟨soko4_2CandidateState192, 51, 192⟩ ⟨soko4_2CandidateState224, 11, 32⟩
    soko4_2Candidate_prefix5_checked soko4_2Candidate_block6_checked

def soko4_2CandidateBlock7 : List Dir := [.west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east, .east, .east, .southEast, .northEast, .west, .west, .east, .northEast, .northWest, .south, .north, .north, .north, .northEast, .southEast, .west, .northWest, .south, .south, .south, .southEast]
def soko4_2CandidateState256 : State := {player := 115, boulders := [114, 129, 127, 113, 50, 51], holes := [31, 46, 61, 76]}
theorem soko4_2Candidate_block7_checked :
    run soko4_2.board soko4_2CandidateState224 soko4_2CandidateBlock7 = some ⟨soko4_2CandidateState256, 8, 32⟩ := by decide

def soko4_2CandidatePrefix7 : List Dir := soko4_2CandidatePrefix6 ++ soko4_2CandidateBlock7
theorem soko4_2Candidate_prefix7_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix7 =
      some ⟨soko4_2CandidateState256, 70, 256⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix6 soko4_2CandidateBlock7
    ⟨soko4_2CandidateState224, 62, 224⟩ ⟨soko4_2CandidateState256, 8, 32⟩
    soko4_2Candidate_prefix6_checked soko4_2Candidate_block7_checked

def soko4_2CandidateBlock8 : List Dir := [.south, .southWest, .northWest, .west, .west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east, .east, .east, .southEast, .northEast, .west, .west, .east, .northEast, .northWest, .south, .southEast, .southWest, .northWest, .west, .west, .west]
def soko4_2CandidateState288 : State := {player := 125, boulders := [121, 129, 113, 50, 51], holes := [31, 46, 61]}
theorem soko4_2Candidate_block8_checked :
    run soko4_2.board soko4_2CandidateState256 soko4_2CandidateBlock8 = some ⟨soko4_2CandidateState288, 6, 32⟩ := by decide

def soko4_2CandidatePrefix8 : List Dir := soko4_2CandidatePrefix7 ++ soko4_2CandidateBlock8
theorem soko4_2Candidate_prefix8_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix8 =
      some ⟨soko4_2CandidateState288, 76, 288⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix7 soko4_2CandidateBlock8
    ⟨soko4_2CandidateState256, 70, 256⟩ ⟨soko4_2CandidateState288, 6, 32⟩
    soko4_2Candidate_prefix7_checked soko4_2Candidate_block8_checked

def soko4_2CandidateBlock9 : List Dir := [.west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east, .east, .east, .southEast, .northEast, .west, .west, .west, .west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east, .east, .east, .northEast]
def soko4_2CandidateState320 : State := {player := 114, boulders := [113, 50, 51], holes := [31]}
theorem soko4_2Candidate_block9_checked :
    run soko4_2.board soko4_2CandidateState288 soko4_2CandidateBlock9 = some ⟨soko4_2CandidateState320, 5, 32⟩ := by decide

def soko4_2CandidatePrefix9 : List Dir := soko4_2CandidatePrefix8 ++ soko4_2CandidateBlock9
theorem soko4_2Candidate_prefix9_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix9 =
      some ⟨soko4_2CandidateState320, 81, 320⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix8 soko4_2CandidateBlock9
    ⟨soko4_2CandidateState288, 76, 288⟩ ⟨soko4_2CandidateState320, 5, 32⟩
    soko4_2Candidate_prefix8_checked soko4_2Candidate_block9_checked

def soko4_2CandidateBlock10 : List Dir := [.northWest, .south, .southEast, .west, .west, .west, .west, .west, .west, .west, .southWest, .north]
def soko4_2CandidateState332 : State := {player := 121, boulders := [50, 51], holes := []}
theorem soko4_2Candidate_block10_checked :
    run soko4_2.board soko4_2CandidateState320 soko4_2CandidateBlock10 = some ⟨soko4_2CandidateState332, 4, 12⟩ := by decide

def soko4_2CandidatePrefix10 : List Dir := soko4_2CandidatePrefix9 ++ soko4_2CandidateBlock10
theorem soko4_2Candidate_prefix10_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePrefix10 =
      some ⟨soko4_2CandidateState332, 85, 332⟩ :=
  run_append_of soko4_2.board soko4_2.initial soko4_2CandidatePrefix9 soko4_2CandidateBlock10
    ⟨soko4_2CandidateState320, 81, 320⟩ ⟨soko4_2CandidateState332, 4, 12⟩
    soko4_2Candidate_prefix9_checked soko4_2Candidate_block10_checked

def soko4_2CandidatePath : List Dir := soko4_2CandidatePrefix10
def soko4_2CandidateFinalState : State := soko4_2CandidateState332

theorem soko4_2_candidate_checked :
    run soko4_2.board soko4_2.initial soko4_2CandidatePath =
      some ⟨soko4_2CandidateFinalState, 85, 332⟩ := soko4_2Candidate_prefix10_checked

theorem soko4_2_candidate_goal : Goal soko4_2CandidateFinalState := by rfl

theorem soko4_2_candidate_trace :
    Trace soko4_2.board soko4_2.initial soko4_2CandidatePath soko4_2CandidateFinalState 85 332 :=
  run_sound _ _ _ _ soko4_2_candidate_checked

end NetHack.Sokoban.Generated
