import Owner1007.Arrival187Four11Data
namespace Owner1007.Arrival187Four11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem singleton_nn {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (cell : Cell) (inside : [cell]⊆state.boulders) : 0≤energy state final [cell] outcomes :=
 HeroLedger.Logged.energy_nonnegative logged (groupCertificate 18)
   (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) [cell] (by simp) inside (by simp)

theorem tail_le {state middle final history beforeDirs dirs past pastMoves beforePushes beforeMoves pushes moves before outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (first : Logged soko1_1.board state beforeDirs middle beforePushes beforeMoves before)
 (last : Logged soko1_1.board middle dirs final pushes moves outcomes)
 (cell : Cell) (inside : [cell]⊆state.boulders) :
 energy middle final (endGroup [cell] before) outcomes≤energy state final [cell] (before++outcomes) := by
 have nn := singleton_nn reached first cell inside
 have split := energy_append state middle final [cell] before outcomes
 omega

theorem head_lower {state middle final history beforeDirs afterDirs past pastMoves beforePushes beforeMoves afterPushes afterMoves before after t cell}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (first : Logged soko1_1.board state beforeDirs middle beforePushes beforeMoves before)
 (head : step soko1_1.board middle .west=some t)
 (effect : Matches middle t (.push cell (.stay (cell-1))))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (member : cell∈([186,187,212]:List Cell)) (inside : [cell]⊆state.boulders)
 (stationary : ownPushes [cell] before=0) :
 2+energy t.state final [cell-1] after≤energy state final [cell] (before++.push cell (.stay (cell-1))::after) := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant (reached.append first.trace)
 have fixed := no_push_unchanged [cell] before stationary
 have facts := first.end_subset valid.1 [cell] (by simp) inside
 rw [fixed] at facts
 have metadata : t.pushSource=some cell := by rw [effect.2]
 have row : 2≤charge NetHack.Soko11Hero315.holeWeight [cell] (.push cell (.stay (cell-1)))+
     value t.state (update [cell] (.push cell (.stay (cell-1))))-value middle [cell] := by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl
   ·exact LeftStrict11.exit_row scalar rfl beforeValid head effect facts.1 facts.2
      ⟨186,by simp,metadata,by simp [LeftActor11.Exit]⟩
   ·exact UpperLocalPrice11.exit_row beforeValid facts.1 facts.2 head effect
      ⟨187,by simp,metadata,by simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources]⟩
   ·exact LeftStrict11.exit_row scalar rfl beforeValid head effect facts.1 facts.2
      ⟨212,by simp,metadata,by simp [LeftActor11.Exit]⟩
 have nn := singleton_nn reached first cell inside
 have split := energy_append state middle final [cell] before (.push cell (.stay (cell-1))::after)
 rw [fixed] at split
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight middle t.state final [cell]
   (.push cell (.stay (cell-1))) after
 change energy middle final [cell] (.push cell (.stay (cell-1))::after)=
   charge NetHack.Soko11Hero315.holeWeight [cell] (.push cell (.stay (cell-1)))+
   value t.state (update [cell] (.push cell (.stay (cell-1))))-value middle [cell]+
   energy t.state final (update [cell] (.push cell (.stay (cell-1)))) after at one
 have updated : update [cell] (.push cell (.stay (cell-1)))=[cell-1] := by simp [update,move,post]
 rw [updated] at one row
 omega

theorem cut_lower {state final history dirs past pastMoves pushes moves outcomes i cell}
 (cut : FirstCut (paid i) state (locks i) dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (inside : [cell]⊆state.boulders) (member : cell∈([186,187,212]:List Cell))
 (stationary : ownPushes [cell] cut.beforeOutcomes=0)
 (metadata : cut.actor.pushSource=some cell) (west : cut.direction=.west) :
 cut.headOutcome=.push cell (.stay (cell-1)) ∧
 2+energy cut.actor.state final [cell-1] cut.afterOutcomes≤energy state final [cell] outcomes := by
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
 have targets : pushTargets soko1_1.board cell .west=[cell-1] := by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl <;> decide +kernel
 have clear : cell-1∉soko1_1.initial.holes := by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl <;> decide +kernel
 have shape := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata targets clear
   (reached.append cut.before.logged.trace).holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push cell (.stay (cell-1))) := by simpa only [shape] using cut.headEffect
 have lower := head_lower reached cut.before.logged checked effect cut.after member inside stationary
 have allShape : outcomes=cut.beforeOutcomes++.push cell (.stay (cell-1))::cut.afterOutcomes := by
   exact cut.outcomesEq.trans (by rw [shape])
 have energySame := congrArg (energy state final [cell]) allShape
 exact ⟨shape,by omega⟩

theorem ticket {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 2) (inside : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone212 : endGroup [212] outcomes=[]) :
 2≤energy state final [front i] outcomes ∨2≤energy state final [212] outcomes := by
 obtain ⟨cut,zero⟩ := first_exit reached logged i inside hero gone212
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 obtain ⟨which,west⟩ := pays
 have cellMember : front i∈([186,187,212]:List Cell) := by
   obtain ⟨v,bound⟩:=i
   have cases:v=0∨v=1:=by omega
   rcases cases with rfl|rfl <;> simp [front]
 have lower (cell : Cell) (member : cell∈([186,187,212]:List Cell)) (inLock : cell∈locks i)
     (metadata : cut.actor.pushSource=some cell) : 2≤energy state final [cell] outcomes := by
   have initial : [cell]⊆state.boulders := by simpa using inside inLock
   have stationary := LeftQuietIdentity11.subset_zero [cell] (locks i) cut.beforeOutcomes (by simpa using inLock) zero
   obtain ⟨shape,bound⟩ := cut_lower cut reached initial member stationary metadata west
   have effect : Matches cut.middle cut.actor (.push cell (.stay (cell-1))) := by simpa only [shape] using cut.headEffect
   have afterReached := (reached.append cut.before.logged.trace).append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
   have afterInside : [cell-1]⊆cut.actor.state.boulders := by rw [effect.2];simp
   have nn := singleton_nn afterReached cut.after (cell-1) afterInside
   omega
 rcases which with same|same
 ·exact Or.inl (lower (front i) cellMember (by simp [locks]) (metadata.trans (congrArg some same)))
 ·exact Or.inr (lower 212 (by simp) (by simp [locks]) (metadata.trans (congrArg some same)))

/-- Clearing the current212 from the right of187/212 costs Left2 or costs
four units to the current187. Neither an arbitrary spare choice nor Goal is assumed. -/
theorem dichotomy {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (inside : [187,212]⊆state.boulders) (hero : state.player=213)
 (gone212 : endGroup [212] outcomes=[]) :
 4≤energy state final [187] outcomes ∨2≤energy state final [212] outcomes := by
 by_cases left : 2≤energy state final [212] outcomes
 ·exact Or.inr left
 ·have initialHero : state.player∈region 0 := by rw [hero];decide +kernel
  obtain ⟨cut,zero⟩ := first_exit reached logged 0 inside initialHero gone212
  obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
  obtain ⟨which,west⟩ := pays
  have in187 : [187]⊆state.boulders := List.Subset.trans (by decide) inside
  have in212 : [212]⊆state.boulders := List.Subset.trans (by decide) inside
  have zero187 := LeftQuietIdentity11.subset_zero [187] (locks 0) cut.beforeOutcomes (by decide) zero
  have zero212 := LeftQuietIdentity11.subset_zero [212] (locks 0) cut.beforeOutcomes (by decide) zero
  rcases which with same|same
  ·have sourceEq : cut.actor.pushSource=some 187 := by simpa [front] using metadata.trans (congrArg some same)
   obtain ⟨shape,lower⟩ := cut_lower cut reached in187 (by simp) zero187 sourceEq west
   change cut.headOutcome=.push 187 (.stay 186) at shape
   change 2+energy cut.actor.state final [186] cut.afterOutcomes≤energy state final [187] outcomes at lower
   have effect : Matches cut.middle cut.actor (.push 187 (.stay 186)) := by simpa only [shape] using cut.headEffect
   let lead := cut.before.logged.append (Logged.cons cut.headChecked cut.headEffect (Logged.nil cut.actor.state))
   have tag : endGroup [212] (cut.beforeOutcomes++[cut.headOutcome])=[212] := by
     rw [endGroup_append,no_push_unchanged [212] cut.beforeOutcomes zero212]
     simp [endGroup,shape,update,move]
   have allShape : (cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes=outcomes := by
     simpa only [List.append_assoc,List.singleton_append] using cut.outcomesEq.symm
   have nextReached := reached.append lead.trace
   have actual212 := lead.end_subset (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1 [212] (by simp) in212
   have nextInside : locks 1⊆cut.actor.state.boulders := by
     change [186,212]⊆cut.actor.state.boulders
     intro c member
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl
     ·rw [effect.2];simp
     ·exact actual212.2 (by rw [tag];simp)
   have nextHero : cut.actor.state.player∈region 1 := by
     rw [effect.2]
     change (187:Cell)∈region 1
     decide +kernel
   have nextGone : endGroup [212] cut.afterOutcomes=[] := by
     rw [←allShape,endGroup_append,tag] at gone212
     exact gone212
   have leftTail := tail_le reached lead cut.after 212 in212
   rw [tag,allShape] at leftTail
   rcases ticket nextReached cut.after 1 nextInside nextHero nextGone with rest|other
   ·change 2≤energy cut.actor.state final [186] cut.afterOutcomes at rest
    exact Or.inl (by omega)
   ·exact False.elim (left (Int.le_trans other leftTail))
  ·have sourceEq : cut.actor.pushSource=some 212 := metadata.trans (congrArg some same)
   obtain ⟨shape,lower⟩ := cut_lower cut reached in212 (by simp) zero212 sourceEq west
   have effect : Matches cut.middle cut.actor (.push 212 (.stay 211)) := by simpa only [shape] using cut.headEffect
   have nextReached := (reached.append cut.before.logged.trace).append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
   have nextInside : [211]⊆cut.actor.state.boulders := by rw [effect.2];simp
   have nn := singleton_nn nextReached cut.after 211 nextInside
   change 2+energy cut.actor.state final [211] cut.afterOutcomes≤energy state final [212] outcomes at lower
   exact False.elim (left (by omega))
#print axioms head_lower
#print axioms ticket
#print axioms dichotomy
end Owner1007.Arrival187Four11
