import Owner1007.UpperShaftGate11
import Owner1007.StrongFirst137EastCore11
import Owner1007.Row13313513711
import Owner1007.Gate139EastImpossible11
namespace Owner1007.StrongShaftGate11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.UpperBudget11
open Owner1007.UpperShaftGate11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem impossible {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (upperCheap : energy soko1_1.initial final U6 (before++outcomes)≤8)
 (restCheap : energy soko1_1.initial final Rest (before++outcomes)≤4)
 (zero137 : ownPushes [137] before=0) (zero139 : ownPushes [139] before=0)
 (i : Fin 3) (hero : state.player∈region i) (inside : locks i⊆state.boulders) : False:=by
 let logged:=first.append last
 obtain ⟨cut⟩:=first_cut first.trace last completed i hero inside
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have good : OwnedCorral11.Good locks region state (locks i):=⟨i,hero,fun _ h=>h⟩
 obtain ⟨j,heroBefore,locksBefore⟩:=Upper216Eight11.quiet_good_any closed unique cut.before
   valid.1 (unique i) inside good first.trace.holes_sublist.subset
 have beforeFacts:=cut.before.logged.end_subset valid.1 (locks i) (unique i) inside
 have beforePhysical:=List.Subset.trans locksBefore beforeFacts.2
 have currentFirst:=first.append cut.before.logged
 have allEffects : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes:=by
   calc
     _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes):=by simp only [List.append_assoc]
     _=before++outcomes:=congrArg (List.append before) cut.outcomesEq.symm
 have stationarity : ∀c∈([137,139] :List Cell), ownPushes [c] (before++cut.beforeOutcomes)=0:=by
   intro c member
   have inLocks : c∈locks i:=by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl <;> simp [locks]
   have localZero:=cut.before.fixed inLocks (by
     intro d
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl <;> simp [paid])
   have initialZero : ownPushes [c] before=0:=by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl
     · exact zero137
     · exact zero139
   rw [ownPushes_append,no_push_unchanged _ _ initialZero,initialZero,localZero]
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 rcases head_shape j heroBefore beforePhysical pays cut.headChecked metadata with ⟨rfl,west⟩|⟨rfl,east⟩
 · have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 137 .west=[136] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 137 (.stay 136)):=by simpa only [headEq] using cut.headEffect
   have eq:=allEffects
   rw [headEq] at eq
   have upper : energy soko1_1.initial final U6
       ((before++cut.beforeOutcomes)++.push 137 (.stay 136)::cut.afterOutcomes)≤8 := by rw [eq];exact upperCheap
   have rest : energy soko1_1.initial final Rest
       ((before++cut.beforeOutcomes)++.push 137 (.stay 136)::cut.afterOutcomes)≤4 := by rw [eq];exact restCheap
   exact Row13313513711.canonical_no_west_with Row13313513711.closed currentFirst checked effect cut.after
     completed (stationarity 137 (by simp)) upper rest
 · have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)):=by simpa only [headEq] using cut.headEffect
   have eq:=allEffects
   rw [headEq] at eq
   have upper : energy soko1_1.initial final U6
       ((before++cut.beforeOutcomes)++.push 139 (.stay 140)::cut.afterOutcomes)≤8 := by rw [eq];exact upperCheap
   exact Gate139EastImpossible11.impossible currentFirst checked effect cut.after completed upper
     (stationarity 139 (by simp))
#print axioms impossible

theorem gate_moved_before_north {state final : State} {t : Transition}
 {beforeDirs afterDirs : List Dir} {beforePushes beforeMoves afterPushes afterMoves : Nat} {before after : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .north=some t) (effect : Matches state t (.push 190 (.stay 164)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (upperCheap : energy soko1_1.initial final U6 (before++.push 190 (.stay 164)::after)≤8)
 (restCheap : energy soko1_1.initial final Rest (before++.push 190 (.stay 164)::after)≤4) :
 0<ownPushes [137] before ∨0<ownPushes [139] before:=by
 by_cases zero137 : ownPushes [137] before=0
 · by_cases zero139 : ownPushes [139] before=0
   · let headLogged : Logged soko1_1.board state [.north] t.state t.pushCost 1 [.push 190 (.stay 164)]:=
       .cons head effect (.nil _)
     let extended:=first.append headLogged
     have tag137:=no_push_unchanged [137] before zero137
     have tag139:=no_push_unchanged [139] before zero139
     have facts137:=first.end_subset (by decide) [137] (by decide) (by decide)
     have facts139:=first.end_subset (by decide) [139] (by decide) (by decide)
     have extended137 : ownPushes [137] (before++[.push 190 (.stay 164)])=0:=by
       rw [ownPushes_append,tag137]
       simpa [ownPushes,ownPush] using zero137
     have extended139 : ownPushes [139] (before++[.push 190 (.stay 164)])=0:=by
       rw [ownPushes_append,tag139]
       simpa [ownPushes,ownPush] using zero139
     have physical : locks 0⊆t.state.boulders:=by
       change [137,139,164]⊆t.state.boulders
       rw [effect.2]
       intro c h
       simp only [List.mem_cons,List.not_mem_nil,or_false] at h
       rcases h with rfl|rfl|rfl
       · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :137≠190)).mpr (facts137.2 (by rw [tag137];simp)))
       · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :139≠190)).mpr (facts139.2 (by rw [tag139];simp)))
       · exact List.mem_cons_self
     have hero : t.state.player∈region 0:=by
       have same : t.state.player=190:=by rw [effect.2]
       rw [same]
       decide +kernel
     have sequence : (before++[.push 190 (.stay 164)])++after=before++.push 190 (.stay 164)::after:=by
       simp only [List.append_assoc,List.singleton_append]
     have upper : energy soko1_1.initial final U6 ((before++[.push 190 (.stay 164)])++after)≤8:=by
       rw [sequence];exact upperCheap
     have rest : energy soko1_1.initial final Rest ((before++[.push 190 (.stay 164)])++after)≤4:=by
       rw [sequence];exact restCheap
     exact False.elim (impossible extended last completed upper rest extended137 extended139 0 hero physical)
   · exact Or.inr (by omega)
 · exact Or.inl (by omega)
#print axioms gate_moved_before_north


end Owner1007.StrongShaftGate11
