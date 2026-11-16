import Owner1007.Guard188Eight11
import Owner1007.BudgetNoReturnBounded11
import Owner1007.Upper190Identity11
import Owner1007.PairFirstCut11
namespace Owner1007.Guard188FourWord11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def G : List Cell := [137,139,188]

theorem zero_cannot_head {paid initial group dirs final pushes moves outcomes cell}
 (cut : UpperFirstCut11.FirstCut paid initial group dirs final pushes moves outcomes)
 (zero : ownPushes [cell] outcomes=0) (metadata : cut.actor.pushSource=some cell) : False := by
 have sum := ownPushes_append [cell] cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have all := congrArg (ownPushes [cell]) cut.outcomesEq
 have beforeZero : ownPushes [cell] cut.beforeOutcomes=0 := by omega
 have tag := no_push_unchanged _ _ beforeZero
 have headOne : ownPush [cell] cut.headOutcome=1 := by
   cases outcomeEq : cut.headOutcome with
   | walk target =>
     have effect : Matches cut.middle cut.actor (.walk target) := by simpa only [outcomeEq] using cut.headEffect
     rw [effect] at metadata
     contradiction
   | push source ending =>
     have effect : Matches cut.middle cut.actor (.push source ending) := by simpa only [outcomeEq] using cut.headEffect
     have same : source=cell := by
       cases ending with
       | stay landing => simpa only [effect.2,Option.some.injEq] using metadata
       | fill hole => simpa only [effect.2.2,Option.some.injEq] using metadata
     subst source
     simp only [ownPush,List.mem_singleton_self,if_true]
 rw [tag] at sum
 simp only [ownPushes,headOne] at sum
 omega

theorem quiet_of_budget {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (stationary137 : ownPushes [137] outcomes=0) (stationary139 : ownPushes [139] outcomes=0)
 (cheap : energy soko1_1.initial state G outcomes<4) :
 UpperQuiet11.Quiet Guard188Eight11.paid soko1_1.initial G dirs state pushes moves outcomes := by
 rcases UpperFirstCut11.first_cut_or_quiet logged G with found|quiet
 · obtain ⟨cut⟩ := found
   have initialGood : OwnedCorral11.Good Guard188Eight11.locks Guard188Eight11.region soko1_1.initial G := by
     refine ⟨0,?_,?_⟩ <;> decide +kernel
   have beforeGood := PairFirstCut11.quiet_good Guard188Eight11.closed Guard188Eight11.unique Guard188Eight11.size cut.before
     (by decide) (by decide) (by decide) (by decide) initialGood (by simp)
   have before := cut.before.logged.end_subset (by decide) G (by decide) (by decide)
   have beforeSize := endGroup_length_le G cut.beforeOutcomes
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have actual := step_boulders_nodup _ _ _ _ valid.1 cut.headChecked
   have nextUnique := GhostSubset.update_unique _ _ _ cut.headEffect actual _ before.1 before.2
   have nextInside := GhostSubset.update_subset _ _ _ cut.headEffect _ before.1 before.2
   have nextBound : (update (endGroup G cut.beforeOutcomes) cut.headOutcome).length≤3 :=
     Nat.le_trans (update_length _ _) beforeSize
   have nextValid := (groupCertificate 3).preserved _ _ _ valid cut.headChecked
   have tailNN := HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 3) nextValid _ nextUnique nextInside nextBound
   change 0≤energy cut.actor.state state (update (endGroup G cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at tailNN
   have split := energy_append soko1_1.initial cut.middle state G cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
   have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state state
     (endGroup G cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
   change energy cut.middle state (endGroup G cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
     RankedCorral11.gap cut.middle cut.actor (endGroup G cut.beforeOutcomes) cut.headOutcome+
     energy cut.actor.state state (update (endGroup G cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
   have all := congrArg (energy soko1_1.initial state G) cut.outcomesEq
   obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
   have forbid_boundary : ∀ c, c∈[187,191] → source=c → UpperLocalPrice11.paid source cut.direction → False := by
     intro c member same paysLocal
     have priced := UpperLocalPrice11.exit_row valid before.1 before.2 cut.headChecked cut.headEffect
       ⟨source,owner,metadata,paysLocal⟩
     change 2≤RankedCorral11.gap cut.middle cut.actor (endGroup G cut.beforeOutcomes) cut.headOutcome at priced
     by_cases prefixLarge : 2≤energy soko1_1.initial cut.middle G cut.beforeOutcomes
     · omega
     · have prefixCheap : energy soko1_1.initial cut.middle G cut.beforeOutcomes<2 := by omega
       have noReturn := BudgetNoReturnBounded11.no_return_quiet (limit:=3) Guard188Eight11.closed Guard188Eight11.unique c
         (Guard188Eight11.priced_landing c member) cut.before NetHack.SokobanLinearPhases.Map11.initial_good
         (by decide) (by decide) (by decide) initialGood (by simp) prefixCheap
       have present : c∈endGroup G cut.beforeOutcomes := same ▸ owner
       have initial := (OneWayToken11.historical cut.before.logged (by decide) c G (by decide) (by decide) noReturn present).1
       have absent : c∉G := by
         simp only [List.mem_cons,List.not_mem_nil,or_false] at member
         rcases member with rfl|rfl <;> decide
       exact absent initial
   rcases pays with rfl|rfl|⟨rfl,directionEq⟩|⟨rfl,directionEq⟩
   · exact False.elim (zero_cannot_head cut stationary137 metadata)
   · exact False.elim (zero_cannot_head cut stationary139 metadata)
   · exact False.elim (forbid_boundary 187 (by decide) rfl (by rw [directionEq]; simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources]))
   · exact False.elim (forbid_boundary 191 (by decide) rfl (by rw [directionEq]; simp [UpperLocalPrice11.paid,UpperLocalPrice11.eastSources]))
 · exact quiet

theorem word {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (stationary137 : ownPushes [137] outcomes=0) (stationary139 : ownPushes [139] outcomes=0)
 (cheap : energy soko1_1.initial state G outcomes<4) :
 ∃i : Fin 8, state.player∈Guard188Eight11.region i ∧ endGroup [188] outcomes=[Guard188Eight11.cell i] := by
 have quiet := quiet_of_budget logged stationary137 stationary139 cheap
 have initialGood : OwnedCorral11.Good Guard188Eight11.locks Guard188Eight11.region soko1_1.initial G := by
   refine ⟨0,?_,?_⟩ <;> decide +kernel
 have good := PairFirstCut11.quiet_good Guard188Eight11.closed Guard188Eight11.unique Guard188Eight11.size quiet
   (by decide) (by decide) (by decide) (by decide) initialGood (by simp)
 obtain ⟨i,heroInside,locksInside⟩ := good
 have part1 := HeroLedger.Logged.end_append_perm logged (by decide) [137] [139,188] (by decide) (by decide)
 have part2 := HeroLedger.Logged.end_append_perm logged (by decide) [139] [188] (by decide) (by decide)
 rw [no_push_unchanged _ _ stationary137] at part1
 rw [no_push_unchanged _ _ stationary139] at part2
 have combined : (endGroup G outcomes).Perm ([137,139]++endGroup [188] outcomes) :=
   part1.trans ((List.Perm.refl [137]).append part2)
 have cellInside : Guard188Eight11.cell i∈endGroup G outcomes := locksInside (by simp [Guard188Eight11.locks])
 have different : Guard188Eight11.cell i≠137 ∧ Guard188Eight11.cell i≠139 := by
   have all : (List.finRange 8).all (fun i => decide (Guard188Eight11.cell i≠137 ∧ Guard188Eight11.cell i≠139))=true := by decide +kernel
   exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
 have markerMember : Guard188Eight11.cell i∈endGroup [188] outcomes := by
   have member := combined.mem_iff.mp cellInside
   simpa [different.1,different.2] using member
 have tag := Upper190Identity11.singleton_member _ (Guard188Eight11.cell i)
   (Nat.le_trans (endGroup_length_le [188] outcomes) (by simp)) markerMember
 exact ⟨i,heroInside,tag⟩
#print axioms word

theorem prefix_two_of_marker {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (stationary137 : ownPushes [137] outcomes=0) (stationary139 : ownPushes [139] outcomes=0)
 (cheap : energy soko1_1.initial state G outcomes<4)
 (c : Cell) (member : c∈[187,191]) (tag : endGroup [188] outcomes=[c]) :
 2≤energy soko1_1.initial state G outcomes := by
 by_cases enough : 2≤energy soko1_1.initial state G outcomes
 · exact enough
 · have cheapTwo : energy soko1_1.initial state G outcomes<2 := by omega
   have quiet := quiet_of_budget logged stationary137 stationary139 cheap
   have initialGood : OwnedCorral11.Good Guard188Eight11.locks Guard188Eight11.region soko1_1.initial G := by
     refine ⟨0,?_,?_⟩ <;> decide +kernel
   have noReturn := BudgetNoReturnBounded11.no_return_quiet (limit:=3) Guard188Eight11.closed Guard188Eight11.unique c
     (Guard188Eight11.priced_landing c member) quiet NetHack.SokobanLinearPhases.Map11.initial_good
     (by decide) (by decide) (by decide) initialGood (by simp) cheapTwo
   have split := HeroLedger.Logged.end_append_perm logged (by decide) [137,139] [188] (by decide) (by decide)
   have present : c∈endGroup G outcomes := split.mem_iff.mpr (List.mem_append_right _ (by rw [tag]; simp))
   have initial := (OneWayToken11.historical logged (by decide) c G (by decide) (by decide) noReturn present).1
   have absent : c∉G := by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl <;> decide
   exact False.elim (absent initial)
#print axioms prefix_two_of_marker

end Owner1007.Guard188FourWord11
