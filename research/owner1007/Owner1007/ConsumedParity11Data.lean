import Owner1007.Hero315Frame11
import Owner1007.TransportQuiet11
namespace Owner1007.ConsumedParity11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

def crates : List Cell := NetHack.SokobanLinearPhases.Map11.certificate.crates 16
def q (cell : Cell) : Int := if (cell/26+cell%26)%2=0 then 1 else 0
def rowCheck (source : Cell) (dir : Dir) : Bool :=
 (pushTargets soko1_1.board source dir).all fun dest=>decide
   (dest≠source→(dest∈crates→(1+q dest-q source)%2=0) ∧
    (dest∈soko1_1.initial.holes→(1-NetHack.Soko11Hero315.holeWeight dest-q source)%2=0))
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase_checked : (List.range 17).all (fun phase=>
 (NetHack.SokobanLinearPhases.Map11.certificate.crates phase).all (fun c=>decide (c∈crates)))=true := by decide +kernel
theorem rows_checked : crates.all (fun source=>allDirs.all (rowCheck source))=true := by decide +kernel
theorem holes_checked : (List.range 17).all (fun phase=>
 (NetHack.SokobanLinearPhases.Map11.certificate.crates phase).all (fun c=>decide (c∉soko1_1.initial.holes.drop phase)))=true := by decide +kernel
theorem initial_checked : soko1_1.initial.boulders.all (fun c=>decide ((q c-weightAt soko1_1.initial c)%2=0))=true := by decide +kernel

theorem crates_subset {state : State}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state) : state.boulders⊆crates := by
 obtain ⟨phase,bound,holes,hero,boxes⟩ := valid.2
 have active : phase<17 := by change phase≤16 at bound;omega
 have row := List.all_eq_true.mp phase_checked phase (List.mem_range.mpr active)
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp row c (boxes member))
theorem row (source dest : Cell) (dir : Dir) (member : source∈crates)
 (target : dest∈pushTargets soko1_1.board source dir) (different : dest≠source) :
 (dest∈crates→(1+q dest-q source)%2=0) ∧
 (dest∈soko1_1.initial.holes→(1-NetHack.Soko11Hero315.holeWeight dest-q source)%2=0) := by
 have checked := List.all_eq_true.mp (List.all_eq_true.mp rows_checked source member) dir (Geometry.all_directions dir)
 exact of_decide_eq_true (List.all_eq_true.mp checked dest target) different
#print axioms rows_checked
#print axioms crates_subset
theorem boxes_noholes {state : State}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state) :
 ∀c∈state.boulders,c∉state.holes := by
 obtain ⟨phase,bound,holes,hero,boxes⟩ := valid.2
 have active : phase<17 := by change phase≤16 at bound;omega
 have row := List.all_eq_true.mp holes_checked phase (List.mem_range.mpr active)
 intro c member
 rw [holes]
 exact of_decide_eq_true (List.all_eq_true.mp row c (boxes member))

theorem stay_distinct {board state dir t source dest dirs final pushes moves outcomes}
 (head : step board state dir=some t) (effect : Matches state t (.push source (.stay dest)))
 (tail : Logged board t.state dirs final pushes moves outcomes) (completed : Goal final) : dest≠source := by
 intro same
 subst dest
 cases tail with
 |nil=>
  have empty : state.holes=[] := by
   have holes : t.state.holes=state.holes := by rw [effect.2]
   change t.state.holes=[] at completed
   exact holes ▸ completed
  have stopped : step board state dir=none := by
   rcases state with ⟨player,boulders,remaining⟩
   cases empty
   cases standing : standingAllowed board ⟨player,boulders,[]⟩ <;>
    simp only [step,standing,Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,bind,pure,Option.bind_some] <;> rfl
  rw [stopped] at head
  contradiction
 |cons checked nextEffect nextTail=>
  have clear := (step_player_clear _ _ _ _ checked).2.2.1
  rw [effect.2] at clear
  exact clear (by simp)
#print axioms boxes_noholes
#print axioms stay_distinct
end Owner1007.ConsumedParity11
