import Owner1007.Inward191Eight11
import Owner1007.LeftQuietIdentity11
import Owner1007.CageFour12
import Owner1007.QuietGroupFixed11
namespace Owner1007.Dead21421511
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def locks (i : Fin 3) : List Cell := match i.val with
 |0=>[187,189,214,215]
 |1=>[186,189,214,215]
 |_=>[186,188,214,215]
def region (i : Fin 3) : List Cell :=
 Inward191Eight11.upper++[190,191,192,193,194,216,217,218,219,220]++if i.val=2 then [189] else []
def q (i : Fin 3) : Cell := if i.val=2 then 188 else 189
def paid (_ : Cell) (_ : Dir) : Prop := True
instance (c : Cell) (d : Dir) : Decidable (paid c d) := by unfold paid;infer_instance
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem size : ∀i,(locks i).length=4:=by decide +kernel
theorem nonempty : ∀i,locks i≠[]:=by decide +kernel
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true:=by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true:=by decide +kernel
theorem floor (i : Fin 3) : region i⊆soko1_1.board.floor:=by
 have row:(List.finRange 3).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c h)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases:i=0∨i=1∨i=2:=by omega
 rcases cases with rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2
theorem phase_closed (i : Fin 3) :
 PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
   (fun _ : Fin 1=>locks i) (fun _ : Fin 1=>region i) paid:=by
 constructor
 ·intro j hero member dir target adjacent isFloor door notLock corner
  exact closed.1 i hero member dir target adjacent isFloor door notLock corner
 ·intro j hero member dir source owner adjacent
  exact Or.inr (Or.inl trivial)
def headCheck (i : Fin 3) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→source=q i∧dir=.west)
theorem heads : ∀i,headCheck i=true:=by decide +kernel
theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 3) (hero : state.player∈region i) (physical : locks i⊆state.boulders)
 (member : source∈locks i) (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) :
 source=q i∧dir=.west:=by
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (heads i) source member) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,behind] at row
 exact of_decide_eq_true row hero (WestRankHead11.source_unblocked checked metadata physical)

theorem first_push {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 3) (physical : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone : endGroup (locks i) outcomes=[]) :
 ∃cut : FirstCut paid state (locks i) dirs final pushes moves outcomes,
 cut.actor.pushSource=some (q i)∧cut.direction=.west∧ownPushes (locks i) cut.beforeOutcomes=0 := by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good : OwnedCorral11.Good locks region state (locks i):=⟨i,hero,List.Subset.refl _⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty logged valid.1 (unique i) physical good reached.holes_sublist.subset gone
 have zero:=QuietGroupFixed11.whole_fixed cut.before (by intro c h d;trivial)
 have fixed:=no_push_unchanged (locks i) cut.beforeOutcomes zero
 have quiet:=LeftQuietIdentity11.quiet_zero_static (locks i) (region i) paid (phase_closed i) (unique i)
    (by intro hero member source owner dir adjacent;exact Or.inr trivial)
    cut.before physical (List.Perm.refl _) hero reached.holes_sublist.subset
 have facts:=cut.before.logged.end_subset valid.1 (locks i) (unique i) physical
 rw [fixed] at facts
 obtain ⟨source,owner,metadata,_⟩:=cut.headPaid
 rw [fixed] at owner
 obtain ⟨same,west⟩:=head_shape i quiet.2 facts.2 owner cut.headChecked metadata
 exact ⟨cut,metadata.trans (congrArg some same),west,zero⟩

theorem terminal_impossible {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 3) (terminal : i.val=0∨i.val=2)
 (physical : locks i⊆state.boulders) (hero : state.player∈region i) (gone : endGroup (locks i) outcomes=[]) : False:=by
 obtain ⟨cut,metadata,west,zero⟩:=first_push reached logged i physical hero gone
 have fixed:=no_push_unchanged (locks i) cut.beforeOutcomes zero
 have beforeReached:=reached.append cut.before.logged.trace
 have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
 have targets : pushTargets soko1_1.board (q i) .west=[q i-1]:=by
  have checked : ∀i:Fin 3,pushTargets soko1_1.board (q i) .west=[q i-1]:=by decide +kernel
  exact checked i
 have noHole : q i-1∉soko1_1.initial.holes:=by
  have checked : ∀i:Fin 3,q i-1∉soko1_1.initial.holes:=by decide +kernel
  exact checked i
 have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata targets noHole beforeReached.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push (q i) (.stay (q i-1))):=by simpa only [outEq] using cut.headEffect
 let frozen : List Cell:=if i.val=0 then [187,188] else [186,187]
 have locked : Locked soko1_1.board frozen:=by
  rcases terminal with zero|two
  ·have same:i=0:=Fin.ext zero
   subst i
   exact locked_of_check _ [187,188] (by decide +kernel)
  ·have same:i=2:=Fin.ext two
   subst i
   exact locked_of_check _ [186,187] (by decide +kernel)
 have shift : frozen⊆update (locks i) (.push (q i) (.stay (q i-1))):=by
  rcases terminal with zero|two
  ·have same:i=0:=Fin.ext zero
   subst i;decide +kernel
  ·have same:i=2:=Fin.ext two
   subst i;decide +kernel
 have facts:=Upper216Eight11.next_facts cut reached (unique i) physical (by rw [size];decide)
 have selected : frozen⊆Upper216Eight11.next cut:=by
  change frozen⊆update (endGroup (locks i) cut.beforeOutcomes) cut.headOutcome
  rw [fixed,outEq];exact shift
 have owns : q i-1∈Upper216Eight11.next cut:=by
  change q i-1∈update (endGroup (locks i) cut.beforeOutcomes) cut.headOutcome
  rw [fixed,outEq]
  have member : q i∈locks i:=by
   have all:∀i:Fin 3,q i∈locks i:=by decide +kernel
   exact all i
  simp [update,move,member,post]
 have mem : q i-1∈frozen:=by
  rcases terminal with zero|two
  ·have same:i=0:=Fin.ext zero
   subst i;decide +kernel
  ·have same:i=2:=Fin.ext two
   subst i;decide +kernel
 have nextReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 exact Upper216Eight11.frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1
   facts.1 facts.2.1 locked (List.Subset.trans selected facts.2.1) mem owns (Upper216Eight11.tail_gone cut gone)

theorem impossible_gone {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 3) (physical : locks i⊆state.boulders) (hero : state.player∈region i) (gone : endGroup (locks i) outcomes=[]) : False:=by
 by_cases middle:i.val=1
 ·have same:i=1:=Fin.ext middle
  subst i
  obtain ⟨cut,metadata,west,zero⟩:=first_push reached logged 1 physical hero gone
  have fixed:=no_push_unchanged (locks 1) cut.beforeOutcomes zero
  have beforeReached:=reached.append cut.before.logged.trace
  have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
  have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 189 .west=[188] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 189 (.stay 188)):=by simpa [outEq,q] using cut.headEffect
  have sameNext : (Upper216Eight11.next cut).Perm (locks 2):=by
   change (update (endGroup (locks 1) cut.beforeOutcomes) cut.headOutcome).Perm _
   rw [fixed,outEq]
   decide +kernel
  have facts:=Upper216Eight11.next_facts cut reached (unique 1) physical (by rw [size];decide)
  have nextPhysical : locks 2⊆cut.actor.state.boulders:=fun c h=>facts.2.1 (sameNext.mem_iff.mpr h)
  have nextHero : cut.actor.state.player∈region 2:=by
   rw [effect.2]
   change (189:Cell)∈region 2
   decide +kernel
  have nextGone : endGroup (locks 2) cut.afterOutcomes=[]:=by
   have goneNext:=Upper216Eight11.tail_gone cut gone
   have same:=endGroup_perm sameNext cut.afterOutcomes
   rw [goneNext] at same
   exact List.perm_nil.mp same.symm
  have nextReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
  exact terminal_impossible nextReached cut.after 2 (Or.inr rfl) nextPhysical nextHero nextGone
 ·have terminal:i.val=0∨i.val=2:=by have bound:=i.isLt;omega
  exact terminal_impossible reached logged i terminal physical hero gone
#print axioms closed
#print axioms impossible_gone
end Owner1007.Dead21421511
