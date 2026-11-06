/- Complete real soko4-1 proposed path. All blocks are checked by the
Lean kernel; the C++ solver and its search/pruning claims are not trusted.
This establishes an upper bound, with no initial-state optimality claim. -/
import NetHack.Sokoban.Maps

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace NetHack.Sokoban.Generated

def soko4_1CandidateBlock0 : List Dir := [.northEast, .east, .east, .west, .west, .west, .west, .west, .northWest, .northWest, .southWest, .east, .east, .southEast, .east, .east, .east, .east, .east, .east, .south, .south, .south, .south, .north, .north, .north, .north, .northWest, .northEast, .south, .south]
def soko4_1CandidateState32 : State := {player := 52, boulders := [66, 122, 53, 32, 44, 106, 121, 135, 148, 150], holes := [88, 86, 100, 114, 142, 143, 144, 145, 146]}
theorem soko4_1Candidate_block0_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidateBlock0 = some ⟨soko4_1CandidateState32, 10, 32⟩ := by decide

def soko4_1CandidatePrefix0 : List Dir := soko4_1CandidateBlock0
theorem soko4_1Candidate_prefix0_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix0 =
      some ⟨soko4_1CandidateState32, 10, 32⟩ := soko4_1Candidate_block0_checked

def soko4_1CandidateBlock1 : List Dir := [.south, .south, .south, .southEast, .south, .southWest, .west, .south, .west, .east, .northEast, .northEast, .north, .northWest, .southWest, .south, .north, .northEast, .southEast, .west, .south, .north, .north, .north, .north, .northWest, .west, .west, .west, .west, .west, .northWest]
def soko4_1CandidateState64 : State := {player := 31, boulders := [136, 107, 135, 134, 53, 32, 44, 106, 150], holes := [88, 86, 100, 114, 142, 143, 144, 145]}
theorem soko4_1Candidate_block1_checked :
    run soko4_1.board soko4_1CandidateState32 soko4_1CandidateBlock1 = some ⟨soko4_1CandidateState64, 8, 32⟩ := by decide

def soko4_1CandidatePrefix1 : List Dir := soko4_1CandidatePrefix0 ++ soko4_1CandidateBlock1
theorem soko4_1Candidate_prefix1_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix1 =
      some ⟨soko4_1CandidateState64, 18, 64⟩ :=
  run_append_of soko4_1.board soko4_1.initial soko4_1CandidatePrefix0 soko4_1CandidateBlock1
    ⟨soko4_1CandidateState32, 10, 32⟩ ⟨soko4_1CandidateState64, 8, 32⟩
    soko4_1Candidate_prefix0_checked soko4_1Candidate_block1_checked

def soko4_1CandidateBlock2 : List Dir := [.northEast, .south, .southWest, .east, .west, .northWest, .southWest, .east, .northEast, .southEast, .east, .east, .east, .east, .east, .northEast, .south, .south, .south, .south, .southEast, .south, .south, .south, .west, .west, .west, .east, .east, .northEast, .northWest, .west]
def soko4_1CandidateState96 : State := {player := 121, boulders := [108, 45, 136, 107, 135, 134, 53, 106], holes := [88, 86, 100, 114, 142, 143, 144]}
theorem soko4_1Candidate_block2_checked :
    run soko4_1.board soko4_1CandidateState64 soko4_1CandidateBlock2 = some ⟨soko4_1CandidateState96, 15, 32⟩ := by decide

def soko4_1CandidatePrefix2 : List Dir := soko4_1CandidatePrefix1 ++ soko4_1CandidateBlock2
theorem soko4_1Candidate_prefix2_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix2 =
      some ⟨soko4_1CandidateState96, 33, 96⟩ :=
  run_append_of soko4_1.board soko4_1.initial soko4_1CandidatePrefix1 soko4_1CandidateBlock2
    ⟨soko4_1CandidateState64, 18, 64⟩ ⟨soko4_1CandidateState96, 15, 32⟩
    soko4_1Candidate_prefix1_checked soko4_1Candidate_block2_checked

def soko4_1CandidateBlock3 : List Dir := [.west, .south, .northEast, .east, .northEast, .northWest, .west, .west, .south, .northEast, .south, .northEast, .southEast, .west, .north, .north, .north, .northWest, .west, .west, .west, .west, .west, .northWest, .southWest, .east, .east, .east, .east, .east, .east, .east]
def soko4_1CandidateState128 : State := {player := 51, boulders := [52, 107, 121, 120, 148, 136, 135, 53], holes := [88, 86, 100, 114, 142, 143, 144]}
theorem soko4_1Candidate_block3_checked :
    run soko4_1.board soko4_1CandidateState96 soko4_1CandidateBlock3 = some ⟨soko4_1CandidateState128, 11, 32⟩ := by decide

def soko4_1CandidatePrefix3 : List Dir := soko4_1CandidatePrefix2 ++ soko4_1CandidateBlock3
theorem soko4_1Candidate_prefix3_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix3 =
      some ⟨soko4_1CandidateState128, 44, 128⟩ :=
  run_append_of soko4_1.board soko4_1.initial soko4_1CandidatePrefix2 soko4_1CandidateBlock3
    ⟨soko4_1CandidateState96, 33, 96⟩ ⟨soko4_1CandidateState128, 11, 32⟩
    soko4_1Candidate_prefix2_checked soko4_1Candidate_block3_checked

def soko4_1CandidateBlock4 : List Dir := [.northEast, .south, .south, .south, .south, .west, .southWest, .south, .north, .northEast, .east, .southEast, .south, .south, .southWest, .west, .west, .east, .east, .northEast, .north, .north, .northWest, .west, .southWest, .south, .south, .north, .north, .northEast, .east, .southEast]
def soko4_1CandidateState160 : State := {player := 109, boulders := [148, 108, 107, 121, 136, 135, 53], holes := [88, 86, 100, 114, 142, 143]}
theorem soko4_1Candidate_block4_checked :
    run soko4_1.board soko4_1CandidateState128 soko4_1CandidateBlock4 = some ⟨soko4_1CandidateState160, 7, 32⟩ := by decide

def soko4_1CandidatePrefix4 : List Dir := soko4_1CandidatePrefix3 ++ soko4_1CandidateBlock4
theorem soko4_1Candidate_prefix4_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix4 =
      some ⟨soko4_1CandidateState160, 51, 160⟩ :=
  run_append_of soko4_1.board soko4_1.initial soko4_1CandidatePrefix3 soko4_1CandidateBlock4
    ⟨soko4_1CandidateState128, 44, 128⟩ ⟨soko4_1CandidateState160, 7, 32⟩
    soko4_1Candidate_prefix3_checked soko4_1Candidate_block4_checked

def soko4_1CandidateBlock5 : List Dir := [.southWest, .west, .east, .northEast, .northWest, .west, .south, .northEast, .southEast, .west, .northWest, .southWest, .south, .north, .northEast, .southEast, .south, .southEast, .southWest, .west, .west, .east, .east, .northEast, .north, .northWest, .northWest, .southWest, .south, .south, .north, .north]
def soko4_1CandidateState192 : State := {player := 106, boulders := [148, 107, 121, 136, 135, 53], holes := [88, 86, 100, 114, 142]}
theorem soko4_1Candidate_block5_checked :
    run soko4_1.board soko4_1CandidateState160 soko4_1CandidateBlock5 = some ⟨soko4_1CandidateState192, 6, 32⟩ := by decide

def soko4_1CandidatePrefix5 : List Dir := soko4_1CandidatePrefix4 ++ soko4_1CandidateBlock5
theorem soko4_1Candidate_prefix5_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix5 =
      some ⟨soko4_1CandidateState192, 57, 192⟩ :=
  run_append_of soko4_1.board soko4_1.initial soko4_1CandidatePrefix4 soko4_1CandidateBlock5
    ⟨soko4_1CandidateState160, 51, 160⟩ ⟨soko4_1CandidateState192, 6, 32⟩
    soko4_1Candidate_prefix4_checked soko4_1Candidate_block5_checked

def soko4_1CandidateBlock6 : List Dir := [.northEast, .southEast, .west, .northWest, .south, .south, .northEast, .southEast, .southEast, .southWest, .west, .west, .east, .east, .northEast, .northWest, .northWest, .southWest, .south, .north, .northEast, .southEast, .west, .northWest, .south, .east, .east, .southEast, .southWest, .west, .west, .west]
def soko4_1CandidateState224 : State := {player := 147, boulders := [142, 134, 136, 135, 53], holes := [88, 86, 100, 114]}
theorem soko4_1Candidate_block6_checked :
    run soko4_1.board soko4_1CandidateState192 soko4_1CandidateBlock6 = some ⟨soko4_1CandidateState224, 8, 32⟩ := by decide

def soko4_1CandidatePrefix6 : List Dir := soko4_1CandidatePrefix5 ++ soko4_1CandidateBlock6
theorem soko4_1Candidate_prefix6_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix6 =
      some ⟨soko4_1CandidateState224, 65, 224⟩ :=
  run_append_of soko4_1.board soko4_1.initial soko4_1CandidatePrefix5 soko4_1CandidateBlock6
    ⟨soko4_1CandidateState192, 57, 192⟩ ⟨soko4_1CandidateState224, 8, 32⟩
    soko4_1Candidate_prefix5_checked soko4_1Candidate_block6_checked

def soko4_1CandidateBlock7 : List Dir := [.west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east, .east, .east, .east, .northEast, .northWest, .west, .west, .south, .northEast, .east, .south, .west, .south, .west, .west, .west, .west, .west, .west, .southWest, .north]
def soko4_1CandidateState256 : State := {player := 142, boulders := [134, 150, 53], holes := [88, 86]}
theorem soko4_1Candidate_block7_checked :
    run soko4_1.board soko4_1CandidateState224 soko4_1CandidateBlock7 = some ⟨soko4_1CandidateState256, 6, 32⟩ := by decide

def soko4_1CandidatePrefix7 : List Dir := soko4_1CandidatePrefix6 ++ soko4_1CandidateBlock7
theorem soko4_1Candidate_prefix7_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix7 =
      some ⟨soko4_1CandidateState256, 71, 256⟩ :=
  run_append_of soko4_1.board soko4_1.initial soko4_1CandidatePrefix6 soko4_1CandidateBlock7
    ⟨soko4_1CandidateState224, 65, 224⟩ ⟨soko4_1CandidateState256, 6, 32⟩
    soko4_1Candidate_prefix6_checked soko4_1Candidate_block7_checked

def soko4_1CandidateBlock8 : List Dir := [.east, .east, .east, .east, .east, .east, .northEast, .northWest, .south, .southEast, .west, .west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .east, .east, .east, .northEast, .southEast, .west, .west, .west, .west, .west]
def soko4_1CandidateState288 : State := {player := 146, boulders := [142, 53], holes := [88]}
theorem soko4_1Candidate_block8_checked :
    run soko4_1.board soko4_1CandidateState256 soko4_1CandidateBlock8 = some ⟨soko4_1CandidateState288, 6, 32⟩ := by decide

def soko4_1CandidatePrefix8 : List Dir := soko4_1CandidatePrefix7 ++ soko4_1CandidateBlock8
theorem soko4_1Candidate_prefix8_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix8 =
      some ⟨soko4_1CandidateState288, 77, 288⟩ :=
  run_append_of soko4_1.board soko4_1.initial soko4_1CandidatePrefix7 soko4_1CandidateBlock8
    ⟨soko4_1CandidateState256, 71, 256⟩ ⟨soko4_1CandidateState288, 6, 32⟩
    soko4_1Candidate_prefix7_checked soko4_1Candidate_block8_checked

def soko4_1CandidateBlock9 : List Dir := [.west, .west, .west, .southWest, .north, .north, .north, .north, .northWest, .east, .east]
def soko4_1CandidateState299 : State := {player := 87, boulders := [53], holes := []}
theorem soko4_1Candidate_block9_checked :
    run soko4_1.board soko4_1CandidateState288 soko4_1CandidateBlock9 = some ⟨soko4_1CandidateState299, 3, 11⟩ := by decide

def soko4_1CandidatePrefix9 : List Dir := soko4_1CandidatePrefix8 ++ soko4_1CandidateBlock9
theorem soko4_1Candidate_prefix9_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePrefix9 =
      some ⟨soko4_1CandidateState299, 80, 299⟩ :=
  run_append_of soko4_1.board soko4_1.initial soko4_1CandidatePrefix8 soko4_1CandidateBlock9
    ⟨soko4_1CandidateState288, 77, 288⟩ ⟨soko4_1CandidateState299, 3, 11⟩
    soko4_1Candidate_prefix8_checked soko4_1Candidate_block9_checked

def soko4_1CandidatePath : List Dir := soko4_1CandidatePrefix9
def soko4_1CandidateFinalState : State := soko4_1CandidateState299

theorem soko4_1_candidate_checked :
    run soko4_1.board soko4_1.initial soko4_1CandidatePath =
      some ⟨soko4_1CandidateFinalState, 80, 299⟩ := soko4_1Candidate_prefix9_checked

theorem soko4_1_candidate_goal : Goal soko4_1CandidateFinalState := by rfl

theorem soko4_1_candidate_trace :
    Trace soko4_1.board soko4_1.initial soko4_1CandidatePath soko4_1CandidateFinalState 80 299 :=
  run_sound _ _ _ _ soko4_1_candidate_checked

end NetHack.Sokoban.Generated
