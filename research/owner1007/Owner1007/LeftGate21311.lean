import Owner1007.LeftQuietIdentity11
import Owner1007.Left188Pocket11
namespace Owner1007.LeftGate21311
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
def front (i : Fin 2) : Cell := if i.val=0 then 213 else 212
def locks (i : Fin 2) : List Cell := [185,187,front i]
def region (i : Fin 2) : List Cell := LeftPair11.H.filter fun c=>
 (if i.val=0 then decide (c<239∨15≤c%26) else true) && !(([183,184,185,186,187,209,210,211,212]++(if i.val=0 then [213] else []) : List Cell).contains c)
def paid (source : Cell) (dir : Dir) : Prop := (source=185∨source=187∨source=212∨source=213)∧dir=.west
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true := by decide +kernel
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor := by
 have row : (List.finRange 2).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c member)
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1 := by omega
 rcases cases with rfl|rfl
 ·exact node0
 ·exact node1
def noMoveCheck (i : Fin 2) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i∨BlockedPush soko1_1.board (locks i) source dir∨paid source dir)
theorem noMove_checked : (List.finRange 2).all noMoveCheck=true := by decide +kernel
theorem noMove (i : Fin 2) : ∀hero∈region i,∀source∈locks i,∀dir,
 advance soko1_1.board hero dir=some source→BlockedPush soko1_1.board (locks i) source dir∨paid source dir := by
 intro hero member source owner dir adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp
   (List.all_eq_true.mp noMove_checked i (by simp)) source owner) dir (Geometry.all_directions dir)
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floor i member) dir source adjacent
 simp only [noMoveCheck,behind] at row
 exact (of_decide_eq_true row).resolve_left (fun h=>h member)
theorem phase_closed (i : Fin 2) :
 PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
  (fun _ : Fin 1=>locks i) (fun _ : Fin 1=>region i) paid := by
 constructor
 ·intro j hero member dir target adjacent isFloor door notLock corner
  exact closed.1 i hero member dir target adjacent isFloor door notLock corner
 ·intro j hero member dir source owner adjacent
  rcases noMove i hero member source owner dir adjacent with blocked|pays
  ·exact Or.inl blocked
  ·exact Or.inr (Or.inl pays)
#print axioms closed
#print axioms noMove
end Owner1007.LeftGate21311

namespace Owner1007.LeftGate21311
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem west187_impossible {paid state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (present185 : 185∈endGroup group cut.beforeOutcomes)
 (sourceEq : cut.actor.pushSource=some 187) (directionEq : cut.direction=.west)
 (gone : endGroup group outcomes=[]) : False := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have beforeReached := reached.append cut.before.logged.trace
 have beforeFacts := cut.before.logged.end_subset valid.1 group unique inside
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [directionEq] using cut.headChecked
 have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect sourceEq
   (show pushTargets soko1_1.board 187 .west=[186] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push 187 (.stay 186)) := by simpa only [headEq] using cut.headEffect
 have nextFacts := Upper216Eight11.next_facts cut reached unique inside bounded
 have afterReached := beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have physical : [185,186]⊆cut.actor.state.boulders := by
   rw [effect.2]
   intro c h
   rcases List.mem_cons.mp h with rfl|later
   · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :185≠187)).mpr (beforeFacts.2 present185))
   · have same : c=186:=List.mem_singleton.mp later
     subst c; exact List.mem_cons_self
 obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
 have same : source=187 := Option.some.inj (metadata.symm.trans sourceEq)
 have owns : 186∈Upper216Eight11.next cut := by
   have owner187 : 187∈endGroup group cut.beforeOutcomes := same ▸ owner
   change 186∈update (endGroup group cut.beforeOutcomes) cut.headOutcome
   rw [headEq]
   simp only [update,move,if_pos owner187,post,List.mem_cons]
   exact Or.inl trivial
 exact Upper216Eight11.frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached).1
   nextFacts.1 nextFacts.2.1 (Owner1007.locked_of_check _ [185,186] (by decide +kernel)) physical (by decide)
   owns (Upper216Eight11.tail_gone cut gone)


theorem first_exit {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (i : Fin 2) (same : group.Perm (locks i)) (hero : state.player∈region i)
 (gone : endGroup group outcomes=[]) :
 ∃cut : FirstCut paid state group dirs final pushes moves outcomes,
  (cut.actor.pushSource=some 185∨cut.actor.pushSource=some (front i))∧
  cut.direction=.west ∧ ownPushes group cut.beforeOutcomes=0 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good : OwnedCorral11.Good (fun _ : Fin 1=>locks i) (fun _ : Fin 1=>region i) state group :=
  ⟨0,hero,fun _ h=>same.mem_iff.mpr h⟩
 obtain ⟨cut⟩ := Upper216Eight11.first_any (phase_closed i) (fun _=>unique i)
   (fun _=>nonempty i) logged valid.1 uniqueGroup inside good reached.holes_sublist.subset gone
 have quiet := LeftQuietIdentity11.quiet_zero_static (locks i) (region i) paid (phase_closed i)
  (unique i) (noMove i) cut.before inside same hero reached.holes_sublist.subset
 have fixed := no_push_unchanged group cut.beforeOutcomes quiet.1
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 have member : source∈locks i := same.mem_iff.mp (by simpa only [fixed] using owner)
 have choices : source=185∨source=187∨source=front i := by
  simpa only [locks,List.mem_cons,List.not_mem_nil,or_false] using member
 rcases choices with rfl|rfl|sameFront
 ·exact ⟨cut,Or.inl metadata,pays.2,quiet.1⟩
 ·have mem185 : 185∈endGroup group cut.beforeOutcomes := by
   rw [fixed]
   exact same.mem_iff.mpr (by simp [locks])
  have bound : group.length≤18 := by
   have len := same.length_eq
   have check : (locks i).length=3 := rfl
   omega
  exact False.elim (west187_impossible cut reached uniqueGroup inside bound mem185 metadata pays.2 gone)
 ·exact ⟨cut,Or.inr (metadata.trans (congrArg some sameFront)),pays.2,quiet.1⟩
#print axioms first_exit
end Owner1007.LeftGate21311
