import Owner1007.LeftTwoLane11Data
import Owner1007.LeftTwoLaneBad11
import Owner1007.RankedCorral11
import Owner1007.QuietAppend11
namespace Owner1007.LeftTwoLaneLift11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.LeftTwoLane11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem pair_unique : ∀i,(locks i).Nodup := by decide +kernel
theorem pair_size : ∀i,(locks i).length=2 := by intro i;rfl
theorem marker_inside : ∀i,left i∈locks i := by intro i;simp [locks]
theorem left185 : ∀i,185∈locks i→left i=185 := by decide +kernel
theorem different : ∀i,left i≠right i := by decide +kernel
theorem one_step
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (refined : RankedCorral11.Refinement locks region left (fun _=>0) paid)
 {beforeDirs state beforePushes beforeMoves before dir t outcome afterDirs final afterPushes afterMoves after}
 (past : UpperQuiet11.Quiet RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (cheapLeft : energy soko1_1.initial final [186] (before++outcome::after)≤2)
 (cheapUpper : energy soko1_1.initial final UpperBudget11.U6 (before++outcome::after)<8)
 (cheapRest : energy soko1_1.initial final UpperBudget11.Rest (before++outcome::after)<2)
 (i : Fin 15) (tagLeft : endGroup [186] before=[left i]) (tagRight : endGroup [188] before=[right i])
 (hero : state.player∈region i) :
 ∃j : Fin 15,update [left i] outcome=[left j]∧update [right i] outcome=[right j]∧t.state.player∈region j := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant past.logged.trace
 have leftFacts := past.logged.end_subset (by decide) [186] (by decide) (by decide)
 have rightFacts := past.logged.end_subset (by decide) [188] (by decide) (by decide)
 have inside : locks i⊆state.boulders := by
  intro c member
  change c∈[left i,right i] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  ·exact leftFacts.2 (by rw [tagLeft];simp)
  ·exact rightFacts.2 (by rw [tagRight];simp)
 have avoid : ¬OwnedCorral11.PaidStep paid (locks i) dir t := by
  intro pays
  obtain ⟨source,owner,metadata,pays⟩:=pays
  rcases pays with ⟨rfl,west⟩|⟨rfl,dirs⟩
  ·have at185 : endGroup [186] before=[185] := by simpa only [left185 i owner] using tagLeft
   have checked : step soko1_1.board state .west=some t := by simpa only [west] using head
   exact LeftTwoLaneBad11.no_west185 past.logged checked effect last at185 metadata cheapLeft
  ·rcases dirs with north|east
   ·have checked : step soko1_1.board state .north=some t := by simpa only [north] using head
    have outEq := UpperHeadCases11.ordinary_effect checked effect metadata
      (show pushTargets soko1_1.board 190 .north=[164] by decide +kernel) (by decide +kernel) past.logged.trace.holes_sublist.subset
    have actualEffect : Matches state t (.push 190 (.stay 164)) := by simpa only [outEq] using effect
    rw [outEq] at cheapUpper cheapRest
    exact LeftTwoLaneBad11.no_north190 past checked actualEffect last completed cheapUpper cheapRest
   ·have checked : step soko1_1.board state .east=some t := by simpa only [east] using head
    have outEq := UpperHeadCases11.ordinary_effect checked effect metadata
      (show pushTargets soko1_1.board 190 .east=[191] by decide +kernel) (by decide +kernel) past.logged.trace.holes_sublist.subset
    have actualEffect : Matches state t (.push 190 (.stay 191)) := by simpa only [outEq] using effect
    have pairPerm := HeroLedger.Logged.end_append_perm past.logged (by decide) [186] [188] (by decide) (by decide)
    rw [tagLeft,tagRight] at pairPerm
    have owns : 190∈endGroup [186,188] before := pairPerm.mem_iff.mpr (by simpa only [locks,List.singleton_append] using owner)
    exact LeftTwoLaneBad11.no_east190 past checked actualEffect owns
 obtain ⟨j,nextHero,nextLocks,leftUpdate,_⟩ := RankedCorral11.step_rank closed pair_unique pair_size marker_inside refined
  valid (pair_unique i) i hero (List.Subset.refl _) inside (by rw [pair_size];exact Nat.le_refl _)
  past.logged.trace.holes_sublist.subset head effect avoid
 let one : Logged soko1_1.board state [dir] t.state t.pushCost 1 [outcome] := .cons head effect (.nil _)
 have split := HeroLedger.Logged.end_append_perm one valid.1 [left i] [right i] (pair_unique i) inside
 change (update (locks i) outcome).Perm (update [left i] outcome++update [right i] outcome) at split
 have rightMember : right j∈update [right i] outcome := by
  have member := split.mem_iff.mp (nextLocks (show right j∈locks j by simp [locks]))
  rcases List.mem_append.mp member with inLeft|inRight
  ·rw [leftUpdate] at inLeft
   have same : right j=left j := List.mem_singleton.mp inLeft
   exact False.elim (different j same.symm)
  ·exact inRight
 have rightUpdate := Upper190Identity11.singleton_member (update [right i] outcome) (right j)
  (Nat.le_trans (update_length _ _) (by simp)) rightMember
 exact ⟨j,leftUpdate,rightUpdate,nextHero⟩
#print axioms one_step
end Owner1007.LeftTwoLaneLift11

namespace Owner1007.LeftTwoLaneLift11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.LeftTwoLane11
theorem guard_aux
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (refined : RankedCorral11.Refinement locks region left (fun _=>0) paid)
 {beforeDirs state beforePushes beforeMoves before group dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (quiet : UpperQuiet11.Quiet RightEarlyWords11.paid state group dirs middle pushes moves outcomes)
 (past : UpperQuiet11.Quiet RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G beforeDirs state beforePushes beforeMoves before)
 (tagEq : group=endGroup RightEarlyWords11.G before)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheapLeft : energy soko1_1.initial final [186] (before++outcomes++last)≤2)
 (cheapUpper : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes++last)<8)
 (cheapRest : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes++last)<2)
 (i : Fin 15) (tagLeft : endGroup [186] before=[left i]) (tagRight : endGroup [188] before=[right i])
 (hero : state.player∈region i) :
 ∃j : Fin 15,endGroup [left i] outcomes=[left j]∧endGroup [right i] outcomes=[right j]∧middle.player∈region j := by
 induction quiet generalizing beforeDirs beforePushes beforeMoves before i with
 |nil=>exact ⟨i,rfl,rfl,hero⟩
 |@cons state group dir t rest middle pushes moves outcome outcomes head effect avoid tail ih=>
  cases tagEq
  have stepLeft : energy soko1_1.initial final [186] (before++outcome::(outcomes++last))≤2 := by
   simpa only [List.append_assoc,List.cons_append] using cheapLeft
  have stepUpper : energy soko1_1.initial final UpperBudget11.U6 (before++outcome::(outcomes++last))<8 := by
   simpa only [List.append_assoc,List.cons_append] using cheapUpper
  have stepRest : energy soko1_1.initial final UpperBudget11.Rest (before++outcome::(outcomes++last))<2 := by
   simpa only [List.append_assoc,List.cons_append] using cheapRest
  obtain ⟨j,leftUpdate,rightUpdate,nextHero⟩ := one_step closed refined past head effect
   (tail.logged.append suffix) completed stepLeft stepUpper stepRest i tagLeft tagRight hero
  let headQuiet : UpperQuiet11.Quiet RightEarlyWords11.paid state (endGroup RightEarlyWords11.G before)
    [dir] t.state t.pushCost 1 [outcome] := .cons head effect avoid (.nil _ _)
  let nextPast := QuietAppend11.Quiet.append past headQuiet
  have nextTagEq : update (endGroup RightEarlyWords11.G before) outcome=endGroup RightEarlyWords11.G (before++[outcome]) := by
   rw [endGroup_append]
   rfl
  have nextLeft : endGroup [186] (before++[outcome])=[left j] := by
   rw [endGroup_append,tagLeft]
   exact leftUpdate
  have nextRight : endGroup [188] (before++[outcome])=[right j] := by
   rw [endGroup_append,tagRight]
   exact rightUpdate
  have nextCheapLeft : energy soko1_1.initial final [186] ((before++[outcome])++outcomes++last)≤2 := by
   simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using cheapLeft
  have nextCheapUpper : energy soko1_1.initial final UpperBudget11.U6 ((before++[outcome])++outcomes++last)<8 := by
   simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using cheapUpper
  have nextCheapRest : energy soko1_1.initial final UpperBudget11.Rest ((before++[outcome])++outcomes++last)<2 := by
   simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using cheapRest
  obtain ⟨k,lastLeft,lastRight,lastHero⟩:=ih nextPast nextTagEq suffix nextCheapLeft nextCheapUpper nextCheapRest j nextLeft nextRight nextHero
  exact ⟨k,by simpa only [endGroup,leftUpdate] using lastLeft,
    by simpa only [endGroup,rightUpdate] using lastRight,lastHero⟩
theorem prefix_word
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (refined : RankedCorral11.Refinement locks region left (fun _=>0) paid)
 {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (quiet : UpperQuiet11.Quiet RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheapLeft : energy soko1_1.initial final [186] (outcomes++last)≤2)
 (cheapUpper : energy soko1_1.initial final UpperBudget11.U6 (outcomes++last)<8)
 (cheapRest : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)<2) :
 ∃j : Fin 15,endGroup [186] outcomes=[left j]∧endGroup [188] outcomes=[right j]∧state.player∈region j := by
 exact guard_aux closed refined quiet (.nil _ _) rfl suffix completed cheapLeft cheapUpper cheapRest
  6 rfl rfl (by decide +kernel)
#print axioms guard_aux
#print axioms prefix_word
end Owner1007.LeftTwoLaneLift11
