import Owner1007.LeftSplit11
import Owner1007.UpperHeadCases11
namespace Owner1007.LeftFirstTwo11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def noMoveCheck (i : Fin 2) : Bool :=
 (LeftPair11.locks i).all fun source=> allDirs.all fun dir=>
  match advance soko1_1.board source dir.opposite with
  | none=>true
  | some hero=>decide (hero∉LeftPair11.region i ∨ BlockedPush soko1_1.board (LeftPair11.locks i) source dir ∨ LeftPair11.paid source dir)
theorem noMove0 : noMoveCheck 0=true := by decide +kernel
theorem noMove1 : noMoveCheck 1=true := by decide +kernel
theorem noMove (i : Fin 2) : noMoveCheck i=true := by
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1:=by omega
 rcases cases with rfl|rfl
 · exact noMove0
 · exact noMove1

def phaseLocks (i : Fin 2) (_ : Fin 1) := LeftPair11.locks i
def phaseRegion (i : Fin 2) (_ : Fin 1) := LeftPair11.region i
theorem phase_closed (i : Fin 2) :
 PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes (phaseLocks i) (phaseRegion i) LeftPair11.paid := by
 constructor
 · intro j hero member dir target adjacent floor door notLock corner
   exact LeftPair11.closed.1 i hero member dir target adjacent floor door notLock corner
 · intro j hero member dir source owner adjacent
   have row := List.all_eq_true.mp (List.all_eq_true.mp (noMove i) source owner) dir (Geometry.all_directions dir)
   have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (LeftPair11.region_floor i member) dir source adjacent
   simp only [noMoveCheck,behind] at row
   rcases (of_decide_eq_true row).resolve_left (fun h=>h member) with blocked|paid
   · exact Or.inl blocked
   · exact Or.inr (Or.inl paid)

theorem pair_perm (i : Fin 2) (group : List Cell) (unique : group.Nodup) (bounded : group.length≤2)
 (inside : LeftPair11.locks i⊆group) : group.Perm (LeftPair11.locks i) := by
 apply (List.perm_ext_iff_of_nodup unique (LeftPair11.unique i)).mpr
 intro c
 constructor
 · intro found
   by_cases member : c∈LeftPair11.locks i
   · exact member
   · have all : c::LeftPair11.locks i⊆group := by
       intro x h
       rcases List.mem_cons.mp h with rfl|later
       · exact found
       · exact inside later
     have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,LeftPair11.unique i⟩) all
     simp only [List.length_cons,LeftPair11.size i] at card
     omega
 · exact fun found=>inside found

theorem quiet_same {state final group dirs pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet LeftPair11.paid state group dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (bounded : group.length≤2) (i : Fin 2) (same : group.Perm (LeftPair11.locks i))
 (hero : state.player∈LeftPair11.region i) (holes : state.holes⊆soko1_1.initial.holes) :
 final.player∈LeftPair11.region i ∧ (endGroup group outcomes).Perm (LeftPair11.locks i) := by
 have good : OwnedCorral11.Good (phaseLocks i) (phaseRegion i) state group :=
   ⟨0,hero,fun _ h=>same.mem_iff.mpr h⟩
 obtain ⟨j,heroLast,locksLast⟩ := PairFirstCut11.quiet_good (phase_closed i)
   (fun _=>LeftPair11.unique i) (fun _=>LeftPair11.size i) quiet actual unique inside bounded good holes
 have facts := quiet.logged.end_subset actual group unique inside
 have len := Nat.le_trans (endGroup_length_le group outcomes) bounded
 exact ⟨heroLast,pair_perm i _ facts.1 len locksLast⟩

def otherSource (i : Fin 2) : Cell := if i.val=0 then 212 else 186
def otherLanding (i : Fin 2) : Cell := if i.val=0 then 211 else 185

theorem other_head {state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut LeftPair11.paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤2)
 (i : Fin 2) (same : group.Perm (LeftPair11.locks i)) (hero : state.player∈LeftPair11.region i)
 (sourceEq : cut.actor.pushSource=some (otherSource i)) :
 (update (endGroup group cut.beforeOutcomes) cut.headOutcome).Perm [185,211] ∧
 cut.actor.state.player∈LeftSplit11.region 0 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have quiet := quiet_same cut.before valid.1 unique inside bounded i same hero reached.holes_sublist.subset
 have beforeReached := reached.append cut.before.logged.trace
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 have sourceSame : source=otherSource i := Option.some.inj (metadata.symm.trans sourceEq)
 have directionEq : cut.direction=.west:=pays.2
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [directionEq] using cut.headChecked
 have targets : pushTargets soko1_1.board (otherSource i) .west=[otherLanding i] := by
   obtain ⟨i,bound⟩:=i
   have cases : i=0∨i=1:=by omega
   rcases cases with rfl|rfl
   · change pushTargets soko1_1.board 212 .west=[211]; decide +kernel
   · change pushTargets soko1_1.board 186 .west=[185]; decide +kernel
 have noHole : otherLanding i∉soko1_1.initial.holes := by
   obtain ⟨i,bound⟩:=i
   have cases : i=0∨i=1:=by omega
   rcases cases with rfl|rfl
   · change 211∉soko1_1.initial.holes; decide +kernel
   · change 185∉soko1_1.initial.holes; decide +kernel
 have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect sourceEq targets noHole beforeReached.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push (otherSource i) (.stay (otherLanding i))) := by simpa only [headEq] using cut.headEffect
 have nextPerm := update_perm quiet.2 cut.headOutcome
 have finalPerm : (update (LeftPair11.locks i) (.push (otherSource i) (.stay (otherLanding i)))).Perm [185,211] := by
   obtain ⟨i,bound⟩:=i
   have cases : i=0∨i=1:=by omega
   rcases cases with rfl|rfl
   · change (update [185,212] (.push 212 (.stay 211))).Perm [185,211]; decide +kernel
   · change (update [186,211] (.push 186 (.stay 185))).Perm [185,211]; decide +kernel
 constructor
 · rw [headEq] at nextPerm ⊢
   exact nextPerm.trans finalPerm
 · have player : cut.actor.state.player=otherSource i := by rw [effect.2]
   rw [player]
   obtain ⟨i,bound⟩:=i
   have cases : i=0∨i=1:=by omega
   rcases cases with rfl|rfl
   · change 212∈LeftSplit11.region 0; decide +kernel
   · change 186∈LeftSplit11.region 0; decide +kernel
#print axioms other_head

theorem six_of_other_second {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (cut : FirstCut LeftPair11.paid state (endGroup [186,212] before) dirs final pushes moves outcomes)
 (completed : Goal final)
 (i : Fin 2) (same : (endGroup [186,212] before).Perm (LeftPair11.locks i))
 (hero : state.player∈LeftPair11.region i)
 (sourceEq : cut.actor.pushSource=some (otherSource i))
 (cashFirst : 1≤PaidCount11.count LeftPair11.paid [186,212] beforeDirs before) :
 6≤energy soko1_1.initial final [186,212] (before++outcomes) := by
 have facts := first.end_subset (by decide) [186,212] (by decide) (by decide)
 have bounded := endGroup_length_le [186,212] before
 change (endGroup [186,212] before).length≤2 at bounded
 obtain ⟨frame,heroAfter⟩ := other_head cut first.trace facts.1 facts.2 bounded i same hero sourceEq
 let headLogged : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
   .cons cut.headChecked cut.headEffect (.nil _)
 let between := cut.before.logged.append headLogged
 let prefixLogged := first.append between
 have prefixFrame : (endGroup [186,212] (before++(cut.beforeOutcomes++[cut.headOutcome]))).Perm [185,211] := by
   rw [endGroup_append,endGroup_append]
   exact frame
 have event := PaidCount11.event_le (lastDirs:=[]) (last:=[]) cut.before.logged cut.headEffect
   (endGroup [186,212] before) cut.headPaid
 have secondCash : 1≤PaidCount11.count LeftPair11.paid (endGroup [186,212] before)
     (cut.beforeDirs++[cut.direction]) (cut.beforeOutcomes++[cut.headOutcome]) := by
   simpa only [PaidCount11.count,Nat.add_zero] using event
 have appendCount := PaidCount11.append first LeftPair11.paid [186,212]
   (cut.beforeDirs++[cut.direction]) (cut.beforeOutcomes++[cut.headOutcome])
 have cash : 2≤PaidCount11.count LeftPair11.paid [186,212]
     (beforeDirs++(cut.beforeDirs++[cut.direction])) (before++(cut.beforeOutcomes++[cut.headOutcome])) := by omega
 have bound := LeftSplit11.six_of_split prefixLogged cut.after completed prefixFrame heroAfter cash
 have shape : (before++(cut.beforeOutcomes++[cut.headOutcome]))++cut.afterOutcomes=before++outcomes := by
   calc
     _ = before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes) := by
       simp only [List.append_assoc,List.singleton_append]
     _ = before++outcomes := congrArg (List.append before) cut.outcomesEq.symm
 simpa only [shape] using bound
#print axioms six_of_other_second

end Owner1007.LeftFirstTwo11

