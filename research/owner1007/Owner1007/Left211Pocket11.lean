import Owner1007.Left188Pocket11
namespace Owner1007.Left211Pocket11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
def locks (_ : Fin 1) : List Cell := [184,186,211]
def region (_ : Fin 1) : List Cell := LeftPair11.H.filter fun c=> !([183,184,185,186,209,210,211] : List Cell).contains c
def paid (source : Cell) (dir : Dir) : Prop := source=211∨(source=186∧dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem floor (i : Fin 1) : region i⊆soko1_1.board.floor := by
 have row : (region 0).all (fun c=>decide (c∈soko1_1.board.floor))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp row c member)
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 have same : i=0 := Fin.ext (by omega)
 simpa only [same] using node
theorem head : Left188Pocket11.headCheck locks region 211 (fun d=>d=.west) 0=true := by decide +kernel
theorem forces_west {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good locks region state group) (gone : endGroup group outcomes=[]) :
 ∃cut : FirstCut paid state group dirs final pushes moves outcomes,
 cut.actor.pushSource=some 211∧cut.direction=.west∧ownPushes [211] cut.beforeOutcomes=0 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 obtain ⟨cut⟩ := Upper216Eight11.first_any closed unique nonempty logged valid.1 uniqueGroup inside good reached.holes_sublist.subset gone
 obtain ⟨i,hero,locksBefore⟩ := Upper216Eight11.quiet_good_any closed unique cut.before valid.1 uniqueGroup inside good reached.holes_sublist.subset
 have beforeFacts := cut.before.logged.end_subset valid.1 group uniqueGroup inside
 have physical := List.Subset.trans locksBefore beforeFacts.2
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 rcases pays with rfl|⟨rfl,west⟩
 ·have sameIndex : i=0 := Fin.ext (by omega)
  have west := Left188Pocket11.head_allowed locks region 211 (fun d=>d=.west) i
    (by simpa only [sameIndex] using head) cut.headChecked metadata hero (step_player_clear _ _ _ _ cut.headChecked).1 physical
  obtain ⟨j,_,startLocks⟩:=good
  have start211 : 211∈group := startLocks (by change 211∈([184,186,211] : List Cell);decide)
  exact ⟨cut,metadata,west,cut.before.fixed start211 (by intro d;exact Or.inl rfl)⟩
 ·exact False.elim (Left188Pocket11.west186_impossible cut reached uniqueGroup inside bounded
    (locksBefore (by change 184∈([184,186,211] : List Cell);decide)) metadata west gone)
#print axioms closed
#print axioms forces_west
end Owner1007.Left211Pocket11

namespace Owner1007.Left211Pocket11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem energy_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good locks region state group) (gone : endGroup group outcomes=[])
 (left : List Cell) (leftUnique : left.Nodup) (leftInside : left⊆state.boulders) (leftBound : left.length≤18)
 (owns211 : 211∈left) :
 2≤energy state final left outcomes := by
 obtain ⟨cut,metadata,west,fixed⟩:=forces_west reached logged group unique inside bounded good gone
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have beforeReached := reached.append cut.before.logged.trace
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have singletonTag := no_push_unchanged [211] cut.beforeOutcomes fixed
 have singletonInside : [211]⊆state.boulders := by simpa using leftInside owns211
 have selected := cut.before.logged.end_mono valid.1 [211] left (by decide) singletonInside
   (by intro c h; have same : c=211:=List.mem_singleton.mp h; exact same ▸ owns211)
 have beforeFacts := cut.before.logged.end_subset valid.1 left leftUnique leftInside
 have owns : 211∈endGroup left cut.beforeOutcomes := selected (by rw [singletonTag]; simp)
 have pays : OwnedCorral11.PaidStep LeftPair11.paid (endGroup left cut.beforeOutcomes) cut.direction cut.actor :=
   ⟨211,owns,metadata,by simp [LeftPair11.paid,west]⟩
 have row := LeftStrict11.exit_row scalar rfl beforeValid cut.headChecked cut.headEffect beforeFacts.1 beforeFacts.2 pays
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup left cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup left cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup left cut.beforeOutcomes) at row
 have prefixNN:=HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18) valid left leftUnique leftInside leftBound
 change 0≤energy state cut.middle left cut.beforeOutcomes at prefixNN
 have afterActual:=step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
 have afterUnique:=GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ beforeFacts.1 beforeFacts.2
 have afterInside:=GhostSubset.update_subset _ _ _ cut.headEffect _ beforeFacts.1 beforeFacts.2
 have afterBound:=Nat.le_trans (update_length (endGroup left cut.beforeOutcomes) cut.headOutcome)
   (Nat.le_trans (endGroup_length_le left cut.beforeOutcomes) leftBound)
 have afterValid:=(groupCertificate 18).preserved _ _ _ beforeValid cut.headChecked
 have tailNN:=HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 18) afterValid
   _ afterUnique afterInside afterBound
 change 0≤energy cut.actor.state final (update (endGroup left cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at tailNN
 have split:=energy_append state cut.middle final left cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup left cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup left cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
   charge NetHack.Soko11Hero315.holeWeight (endGroup left cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup left cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup left cut.beforeOutcomes)+
   energy cut.actor.state final (update (endGroup left cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 have same:=congrArg (energy state final left) cut.outcomesEq
 omega

#print axioms energy_two
end Owner1007.Left211Pocket11
