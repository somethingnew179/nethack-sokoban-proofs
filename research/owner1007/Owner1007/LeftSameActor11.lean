import Owner1007.LeftActorCount11
import Owner1007.TightSurvivors11
namespace Owner1007.LeftSameActor11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def original (i : Fin 2) : Cell := if i.val=0 then 186 else 212
def landing (i : Fin 2) : Cell := if i.val=0 then 185 else 211
theorem original_member : ∀i,original i∈([186,212] : List Cell) := by decide +kernel
theorem landing_member : ∀i,landing i∈LeftPair11.locks i := by decide +kernel
theorem source_cases : ∀i,∀source∈LeftPair11.locks i,
 source=landing i∨source=LeftFirstTwo11.otherSource i := by decide +kernel
theorem shift_pair : ∀i,(update [186,212] (.push (original i) (.stay (landing i)))).Perm (LeftPair11.locks i) := by decide +kernel
theorem shift_single : ∀i,update [original i] (.push (original i) (.stay (landing i)))=[landing i] := by decide +kernel
theorem hero_after : ∀i,original i∈LeftPair11.region i := by decide +kernel
theorem targets : ∀i,pushTargets soko1_1.board (original i) .west=[landing i] := by decide +kernel
theorem no_hole : ∀i,landing i∉soko1_1.initial.holes := by decide +kernel
theorem landing_paid : ∀i,LeftPair11.paid (landing i) .west := by decide +kernel
theorem original_paid : ∀i,LeftPair11.paid (original i) .west := by decide +kernel

/-- At tight Left energy four, the first two obligatory West pushes have
the same ORIGINAL owner; splitting them between the two stones costs six. -/
theorem count_two_one_actor {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (cheapLeft : energy soko1_1.initial final [186,212] outcomes≤4)
 (consumed : endGroup [186,212] outcomes=[]) :
 2≤PaidCount11.count LeftPair11.paid [186] dirs outcomes ∨
 2≤PaidCount11.count LeftPair11.paid [212] dirs outcomes := by
 have initialGood : OwnedCorral11.Good LeftPair11.cut0Locks LeftPair11.cut0Region soko1_1.initial [186,212] := by
   refine ⟨0,?_,?_⟩ <;> decide +kernel
 obtain ⟨first⟩ := LeftWestCount11.find LeftPair11.first_closed LeftEnergy11.first_unique LeftEnergy11.first_size
   (Trace.nil soko1_1.initial) logged [186,212] (by decide) (by decide) (by decide) initialGood consumed
 have firstZero := LeftQuietIdentity11.first_quiet_zero first.before (by decide)
   (List.Perm.refl _) (by decide +kernel) (by simp)
 have firstPair := no_push_unchanged [186,212] first.beforeOutcomes firstZero
 obtain ⟨source,owner,metadata,sources,west⟩ := first.headPaid
 obtain ⟨i,firstSource⟩ : ∃i : Fin 2,first.actor.pushSource=some (original i) := by
   rcases sources with rfl|rfl
   · exact ⟨0,metadata⟩
   · exact ⟨1,metadata⟩
 have headEq := UpperHeadCases11.ordinary_effect first.headChecked first.headEffect firstSource
   (by simpa only [west] using targets i) (no_hole i) first.before.logged.trace.holes_sublist.subset
 have headHero : first.actor.state.player=original i := by
   have effect : Matches first.middle first.actor (.push (original i) (.stay (landing i))) := by
     simpa only [headEq] using first.headEffect
   rw [effect.2]
 let lead : List Outcome := first.beforeOutcomes++[first.headOutcome]
 let leadDirs : List Dir := first.beforeDirs++[first.direction]
 let headLogged : Logged soko1_1.board first.middle [first.direction] first.actor.state first.actor.pushCost 1 [first.headOutcome] :=
   .cons first.headChecked first.headEffect (.nil _)
 let leadLogged : Logged soko1_1.board soko1_1.initial leadDirs first.actor.state
     (first.beforePushes+first.actor.pushCost) (first.beforeMoves+1) lead := first.before.logged.append headLogged
 let group := endGroup [186,212] lead
 have groupEq : group=update [186,212] (.push (original i) (.stay (landing i))) := by
   simp only [group,lead,endGroup_append,endGroup,firstPair,headEq]
 have same : group.Perm (LeftPair11.locks i) := by rw [groupEq];exact shift_pair i
 have hero : first.actor.state.player∈LeftPair11.region i := by rw [headHero];exact hero_after i
 have facts := leadLogged.end_subset (by decide) [186,212] (by decide) (by decide)
 have bounded : group.length≤2 := endGroup_length_le [186,212] lead
 have good : OwnedCorral11.Good LeftPair11.locks LeftPair11.region first.actor.state group :=
   ⟨i,hero,fun _ h=>same.mem_iff.mpr h⟩
 have shape : outcomes=lead++first.afterOutcomes := by
   exact first.outcomesEq.trans (by simp only [lead,List.append_assoc,List.singleton_append])
 have gone : endGroup group first.afterOutcomes=[] := by
   rw [shape,endGroup_append] at consumed
   exact consumed
 obtain ⟨second⟩ := LeftWestCount11.find LeftPair11.closed LeftPair11.unique LeftPair11.size
   leadLogged.trace first.after group facts.1 facts.2 bounded good gone
 have secondZero := LeftQuietIdentity11.phase_quiet_zero second.before facts.2 i same hero leadLogged.trace.holes_sublist.subset
 have secondPair := no_push_unchanged group second.beforeOutcomes secondZero
 obtain ⟨source2,owner2,metadata2,paid2⟩ := second.headPaid
 have secondMember : source2∈LeftPair11.locks i := by
   rw [secondPair] at owner2
   exact same.mem_iff.mp owner2
 have cashFirst : 1≤PaidCount11.count LeftPair11.paid [186,212] leadDirs lead := by
   have paid : OwnedCorral11.PaidStep LeftPair11.paid (endGroup [186,212] first.beforeOutcomes) first.direction first.actor := by
     refine ⟨original i,?_,firstSource,?_⟩
     · rw [firstPair];exact original_member i
     · simpa only [west] using original_paid i
   have bound := PaidCount11.event_le (lastDirs:=[]) (last:=[]) first.before.logged first.headEffect [186,212] paid
   simpa only [PaidCount11.count,Nat.add_zero] using bound
 have sameActor : source2=landing i := by
   rcases source_cases i source2 secondMember with sameActor|otherActor
   · exact sameActor
   · have otherSource : second.actor.pushSource=some (LeftFirstTwo11.otherSource i) := by rw [metadata2,otherActor]
     have six := LeftFirstTwo11.six_of_other_second leadLogged second completed i same hero otherSource cashFirst
     rw [←shape] at six
     omega
 have actorBefore : endGroup [original i] first.beforeOutcomes=[original i] := by
   apply no_push_unchanged
   exact LeftQuietIdentity11.subset_zero [original i] [186,212] first.beforeOutcomes
     (by simpa using original_member i) firstZero
 have actorAfter : update (endGroup [original i] first.beforeOutcomes) first.headOutcome=[landing i] := by
   rw [actorBefore,headEq]
   exact shift_single i
 have actorBetween : endGroup [landing i] second.beforeOutcomes=[landing i] := by
   apply no_push_unchanged
   apply LeftQuietIdentity11.subset_zero [landing i] group second.beforeOutcomes
   · intro c found
     have eq : c=landing i := List.mem_singleton.mp found
     rw [eq]
     exact same.mem_iff.mpr (landing_member i)
   · exact secondZero
 have firstOwned : OwnedCorral11.PaidStep LeftPair11.paid (endGroup [original i] first.beforeOutcomes) first.direction first.actor := by
   refine ⟨original i,?_,firstSource,?_⟩
   · rw [actorBefore];simp
   · simpa only [west] using original_paid i
 have secondOwned : OwnedCorral11.PaidStep LeftPair11.paid (endGroup [landing i] second.beforeOutcomes) second.direction second.actor := by
   refine ⟨source2,?_,metadata2,paid2⟩
   rw [actorBetween,sameActor]
   simp
 have secondCount := PaidCount11.event_le (lastDirs:=second.afterDirs) (last:=second.afterOutcomes)
   second.before.logged second.headEffect [landing i] secondOwned
 rw [←second.dirsEq,←second.outcomesEq] at secondCount
 have afterCount : 1≤PaidCount11.count LeftPair11.paid [landing i] first.afterDirs first.afterOutcomes := by omega
 have firstCount := PaidCount11.event_le (lastDirs:=first.afterDirs) (last:=first.afterOutcomes)
   first.before.logged first.headEffect [original i] firstOwned
 rw [actorAfter,←first.dirsEq,←first.outcomesEq] at firstCount
 have twice : 2≤PaidCount11.count LeftPair11.paid [original i] dirs outcomes := by omega
 have cases : original i=186∨original i=212 := by
   exact List.mem_cons.mp (original_member i) |>.imp_right List.mem_singleton.mp
 rcases cases with eq|eq
 · exact Or.inl (by simpa only [eq] using twice)
 · exact Or.inr (by simpa only [eq] using twice)

theorem canonical_count_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325) :
 2≤PaidCount11.count LeftPair11.paid [186] dirs outcomes ∨
 2≤PaidCount11.count LeftPair11.paid [212] dirs outcomes := by
 have left := (Tight32511.budgets logged completed cheap).2.2.1
 change energy soko1_1.initial final [186,212] outcomes=4 at left
 have gone : endGroup [186,212] outcomes=[] := by
   apply TightSurvivors11.all_nil logged (by decide) [186,212] (by decide) (by decide)
   intro cell member
   apply TightSurvivors11.singleton_nil logged completed [186,212] (by decide) (by decide) (by decide) 4 (by omega) cell member
   have check : ([186,212] : List Cell).all (fun c=>decide (value soko1_1.initial [c]< -4))=true := by decide +kernel
   exact of_decide_eq_true (List.all_eq_true.mp check cell member)
 exact count_two_one_actor logged completed (by omega) gone

theorem canonical_actor_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325) :
 4≤energy soko1_1.initial final [186] outcomes ∨4≤energy soko1_1.initial final [212] outcomes := by
 rcases canonical_count_two logged completed cheap with first|second
 · exact Or.inl (LeftActorCount11.actor_four logged 186 (by decide) first)
 · exact Or.inr (LeftActorCount11.actor_four logged 212 (by decide) second)
#print axioms count_two_one_actor
#print axioms canonical_count_two
#print axioms canonical_actor_four
end Owner1007.LeftSameActor11
