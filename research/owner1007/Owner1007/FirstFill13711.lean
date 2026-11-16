import Owner1007.Upper216Eight11
import Owner1007.Upper190Identity11
import Owner1007.PairPost11
namespace Owner1007.FirstFill13711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def chamber : List Cell := [27,28,29,30,31,32,53,54,55,56,57,58,59,85]
def ingressCheck : Bool :=
 NetHack.SokobanLinearPhases.Map11.cratesRegion0.all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 | none=>true
 | some hero=>decide (source∈chamber ∨ hero∉soko1_1.board.floor ∨ hero=137 ∨
     ∀dest∈pushTargets soko1_1.board source dir, dest∉chamber ∧ dest∉soko1_1.initial.holes)
theorem ingress : ingressCheck=true := by decide +kernel

theorem at_zero {state : State} {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (same : state.holes=soko1_1.initial.holes) :
 state.boulders⊆NetHack.SokobanLinearPhases.Map11.cratesRegion0 := by
 obtain ⟨phase,atIndex⟩ := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).2
 have pEq:=HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 have phaseZero : phase=0 := by
   rw [pEq]
   simp only [HazardPhaseCountedCorrection.phaseOf,same,Nat.sub_self]
 rw [phaseZero] at atIndex
 exact atIndex.2.2.2

theorem ingress_row {state : State} {dir : Dir} {t : Transition} {source dest : Cell}
 (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source)
 (sourceInside : source∈NetHack.SokobanLinearPhases.Map11.cratesRegion0)
 (absent : source∉chamber) (fixed : 137∈state.boulders)
 (target : dest∈pushTargets soko1_1.board source dir) :
 dest∉chamber ∧ dest∉soko1_1.initial.holes := by
 have adjacent:=PairPost11.source_adjacent checked metadata
 have floor:=(step_player_clear _ _ _ _ checked).1
 have different : state.player≠137 := by
   intro eq
   exact (step_player_clear _ _ _ _ checked).2.2.1 (eq ▸ fixed)
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player floor dir source adjacent
 have row:=List.all_eq_true.mp (List.all_eq_true.mp ingress source sourceInside) dir (Geometry.all_directions dir)
 simp only [ingressCheck,behind] at row
 exact (((of_decide_eq_true row).resolve_left absent).resolve_left (fun h=>h floor)).resolve_left different dest target

theorem nofill_locked137 {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (same : state.holes=soko1_1.initial.holes) (present : 137∈state.boulders)
 (empty : ∀c∈state.boulders, c∉chamber) (stationary : ownPushes [137] outcomes=0) :
 final.holes=soko1_1.initial.holes ∧ (∀c∈final.boulders, c∉chamber) := by
 induction logged generalizing history past pastMoves with
 | nil => exact ⟨same,empty⟩
 | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
   have ownZero : ownPush [137] outcome=0 := by simp only [ownPushes] at stationary;omega
   have unchanged:=ownPush_zero_update [137] outcome ownZero
   have tailZero : ownPushes [137] outcomes=0 := by
     simpa only [ownPushes,ownZero,unchanged,Nat.zero_add] using stationary
   have nextFixed:=GhostSubset.update_subset state t outcome effect [137] (by decide) (by simpa using present)
   rw [unchanged] at nextFixed
   have nextPresent : 137∈t.state.boulders:=nextFixed (by simp)
   have nextReached:=reached.append (Trace.cons head (Trace.nil t.state))
   have next : t.state.holes=soko1_1.initial.holes ∧ (∀c∈t.state.boulders,c∉chamber) := by
     cases outcome with
     | walk target =>
       have holesEq : t.state.holes=state.holes:=congrArg (fun x : Transition=>x.state.holes) effect
       have boxesEq : t.state.boulders=state.boulders:=congrArg (fun x : Transition=>x.state.boulders) effect
       rw [holesEq,boxesEq]
       exact ⟨same,empty⟩
     | push source ending =>
       cases ending with
       | stay dest =>
         have sourcePresent : source∈state.boulders:=effect.1
         have crates:=at_zero reached same sourcePresent
         have sourceOutside:=empty source sourcePresent
         have metadata : t.pushSource=some source:=by rw [effect.2]
         have geometry:=UpperQuiet11.stay_geometry head effect
         have row:=ingress_row head metadata crates sourceOutside present geometry.2
         constructor
         · rw [effect.2];exact same
         · intro c found
           have shape : t.state.boulders=dest::state.boulders.erase source:=by rw [effect.2]
           rw [shape] at found
           rcases List.mem_cons.mp found with rfl|old
           · exact row.1
           · exact empty c (List.mem_of_mem_erase old)
       | fill hole =>
         have sourcePresent : source∈state.boulders:=effect.1
         have crates:=at_zero reached same sourcePresent
         have sourceOutside:=empty source sourcePresent
         have metadata : t.pushSource=some source:=by rw [effect.2.2]
         obtain ⟨landing,landed,target⟩:=LeftEnergy11.push_landing head metadata
         have landingEq : landing=hole := by
           have expected : t.landing=some hole:=by rw [effect.2.2]
           exact Option.some.inj (landed.symm.trans expected)
         have row:=ingress_row head metadata crates sourceOutside present target
         have member : hole∈soko1_1.initial.holes:=same ▸ effect.2.1
         exact False.elim (row.2 (landingEq.symm ▸ member))
   exact ih nextReached next.1 nextPresent next.2 tailZero

theorem no_fill_before137_moves {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (stationary : ownPushes [137] outcomes=0) :
 state.holes=soko1_1.initial.holes := by
 exact (nofill_locked137 (Trace.nil _) logged rfl (by decide +kernel)
   (by decide +kernel) stationary).1

theorem moved_before_hole_change {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (changed : state.holes≠soko1_1.initial.holes) :
 0<ownPushes [137] outcomes := by
 have positive : ownPushes [137] outcomes≠0 := fun zero=>changed (no_fill_before137_moves logged zero)
 omega
#print axioms no_fill_before137_moves
#print axioms moved_before_hole_change
end Owner1007.FirstFill13711

