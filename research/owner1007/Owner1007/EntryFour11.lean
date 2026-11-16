import Owner1007.PostEnergy11
import NetHack.Sokoban.Reduction
import Owner1007.HeroEnergyTrace11
import Owner1007.UpperFirstCut11
import Owner1007.UpperHeadCases11
import Owner1007.StationaryExit11
namespace Owner1007.EntryFour11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.LowerBounds
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def locks (_ : Fin 1) : List Cell := [139,114]
def region (_ : Fin 1) : List Cell := PostCuts11.without PostCuts11.H [139,140,141,142,114,115,116]
def paid (source : Cell) (dir : Dir) : Prop := (source=139 ∨ source=114) ∧ dir=.east
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
def locks3 (_ : Fin 1) : List Cell := [139,141,113]
def region3 (_ : Fin 1) : List Cell := PostCuts11.entryRegion 0
def paid3 (source : Cell) (dir : Dir) : Prop := (source=139 ∨ source=113) ∧ dir=.east
instance (c : Cell) (d : Dir) : Decidable (paid3 c d) := by unfold paid3; infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem walk_north : FastCorral11.walkPart soko1_1.board locks region 0 .north=true := by decide +kernel
theorem walk_south : FastCorral11.walkPart soko1_1.board locks region 0 .south=true := by decide +kernel
theorem walk_east : FastCorral11.walkPart soko1_1.board locks region 0 .east=true := by decide +kernel
theorem walk_west : FastCorral11.walkPart soko1_1.board locks region 0 .west=true := by decide +kernel
theorem walk_northEast : FastCorral11.walkPart soko1_1.board locks region 0 .northEast=true := by decide +kernel
theorem walk_northWest : FastCorral11.walkPart soko1_1.board locks region 0 .northWest=true := by decide +kernel
theorem walk_southEast : FastCorral11.walkPart soko1_1.board locks region 0 .southEast=true := by decide +kernel
theorem walk_southWest : FastCorral11.walkPart soko1_1.board locks region 0 .southWest=true := by decide +kernel
theorem walk3_north : FastCorral11.walkPart soko1_1.board locks3 region3 0 .north=true := by decide +kernel
theorem walk3_south : FastCorral11.walkPart soko1_1.board locks3 region3 0 .south=true := by decide +kernel
theorem walk3_east : FastCorral11.walkPart soko1_1.board locks3 region3 0 .east=true := by decide +kernel
theorem walk3_west : FastCorral11.walkPart soko1_1.board locks3 region3 0 .west=true := by decide +kernel
theorem walk3_northEast : FastCorral11.walkPart soko1_1.board locks3 region3 0 .northEast=true := by decide +kernel
theorem walk3_northWest : FastCorral11.walkPart soko1_1.board locks3 region3 0 .northWest=true := by decide +kernel
theorem walk3_southEast : FastCorral11.walkPart soko1_1.board locks3 region3 0 .southEast=true := by decide +kernel
theorem walk3_southWest : FastCorral11.walkPart soko1_1.board locks3 region3 0 .southWest=true := by decide +kernel
theorem push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem push3 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks3 region3 paid3 0=true := by decide +kernel

theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem unique3 : ∀ i, (locks3 i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=2 := by decide +kernel
theorem size3 : ∀ i, (locks3 i).length=3 := by decide +kernel
theorem debt139 : (List.range 16).all (fun p => decide (NetHack.Soko11Hero315.weight p 112 139≤-4)) = true := by decide +kernel
theorem debt_pair : (List.range 16).all (fun p => decide (weightSum (NetHack.Soko11Hero315.weight p 113) [139,114]≤-2)) = true := by decide +kernel
theorem price114 : (List.range 16).all (fun p => decide (ActorPrices11.price p 113 114 115=2)) = true := by decide +kernel
theorem no_self : [139,141,113].all (fun source => allDirs.all (fun dir => decide (source∉pushTargets soko1_1.board source dir)))=true := by decide +kernel

theorem floor (i : Fin 1) : region i⊆soko1_1.board.floor := by
 have all : (region 0).all (fun c => decide (c∈soko1_1.board.floor))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp all c found)
theorem floor3 (i : Fin 1) : region3 i⊆soko1_1.board.floor := PostCuts11.entry_floor 0
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 have same : i=0 := Fin.ext (by omega)
 rw [same]
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir
   · exact walk_north
   · exact walk_south
   · exact walk_east
   · exact walk_west
   · exact walk_northEast
   · exact walk_northWest
   · exact walk_southEast
   · exact walk_southWest
 · exact push
theorem closed3 : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks3 region3 paid3 := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor3
 intro i
 have same : i=0 := Fin.ext (by omega)
 rw [same]
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir
   · exact walk3_north
   · exact walk3_south
   · exact walk3_east
   · exact walk3_west
   · exact walk3_northEast
   · exact walk3_northWest
   · exact walk3_southEast
   · exact walk3_southWest
 · exact push3

theorem unchanged {state : State} {dir : Dir} {t : Transition} {outcome : Outcome}
 (checked : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (afterInside : [139,141,113]⊆update [139,141,113] outcome) :
 (∀ group, group⊆[139,141,113] → update group outcome=group) := by
 intro group inside
 cases outcome with
 | walk _ => rfl
 | push source ending =>
   by_cases owner : source∈[139,141,113]
   · have remains := afterInside owner
     have unique : ([139,141,113] : List Cell).Nodup := by decide
     have gone := unique.not_mem_erase (a:=source)
     cases ending with
     | stay landing =>
       have target := (UpperQuiet11.stay_geometry checked effect).2
       have row := List.all_eq_true.mp no_self source owner
       have notSelf := of_decide_eq_true (List.all_eq_true.mp row dir (Geometry.all_directions dir))
       have different : landing≠source := by intro same; subst landing; exact notSelf target
       change source ∈ (if source∈[139,141,113] then post [139,141,113] source (.stay landing) else [139,141,113]) at remains
       rw [if_pos owner] at remains
       simp only [post,List.mem_cons] at remains
       exact False.elim (remains.elim (fun same => different same.symm) gone)
     | fill hole =>
       change source ∈ (if source∈[139,141,113] then post [139,141,113] source (.fill hole) else [139,141,113]) at remains
       rw [if_pos owner] at remains
       change source∈([139,141,113] : List Cell).erase source at remains
       exact False.elim (gone remains)
   · have notOwn : source∉group := fun found => owner (inside found)
     simp only [update,move,if_neg notOwn]

theorem quiet_fixed {state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid3 state group dirs final pushes moves outcomes)
 (same : group=[139,141,113])
 (actualUnique : state.boulders.Nodup) (inside : [139,141,113]⊆state.boulders)
 (hero : state.player∈region3 0) (holesInside : state.holes⊆soko1_1.initial.holes)
 (selected : List Cell) (selectedInside : selected⊆[139,141,113]) :
 final.player∈region3 0 ∧ endGroup [139,141,113] outcomes=[139,141,113] ∧
 endGroup selected outcomes=selected := by
 induction quiet with
 | nil => exact ⟨hero,rfl,rfl⟩
 | @cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih =>
   subst group
   have good : OwnedCorral11.Good locks3 region3 state [139,141,113] := ⟨0,hero,by intro c h; exact h⟩
   have nextGood := OwnedCorral11.step_good_except closed3 unique3 size3 good inside (by decide) holesInside checked effect avoid
   obtain ⟨i,nextHero,nextInside⟩ := nextGood
   have complete : [139,141,113]⊆update [139,141,113] outcome := nextInside
   have stays := unchanged checked effect complete
   have groupStay := stays [139,141,113] (by intro c h; exact h)
   have pairStay := stays selected selectedInside
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
   have nextSelected := GhostSubset.update_subset state t outcome effect [139,141,113] (by decide) inside
   rw [groupStay] at nextSelected
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ checked).subset holesInside
   obtain ⟨heroLast,groupLast,pairLast⟩ := ih groupStay nextActual nextSelected nextHero nextHoles
   exact ⟨heroLast,by simpa only [endGroup,groupStay] using groupLast,
     by simpa only [endGroup,pairStay] using pairLast⟩
#print axioms quiet_fixed

theorem east_support {state : State} {t : Transition} {source : Cell}
 (checked : step soko1_1.board state .east=some t) (sourceEq : t.pushSource=some source) :
 advance soko1_1.board state.player .east=some source := by
 rcases step_cases_full _ _ _ _ checked with walked|pushed
 · obtain ⟨target,_,_,_,_,shape⟩ := walked
   simp only [shape] at sourceEq
   contradiction
 · obtain ⟨other,result,adjacent,_,_,_,shape⟩ := pushed
   have same : other=source := by simpa only [shape,Option.some.injEq] using sourceEq
   simpa only [same] using adjacent

theorem exit_row {state : State} {direction : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
 (good : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (checked : step soko1_1.board state direction=some t) (effect : Matches state t outcome)
 (unique : group.Nodup) (inside : group⊆state.boulders)
 (pays : OwnedCorral11.PaidStep paid group direction t) :
 2≤charge (groupCertificate 2).holeWeight group outcome +
   value t.state (update group outcome)-value state group := by
 obtain ⟨source,owner,metadata,pays⟩ := pays
 rcases pays with ⟨rfl|rfl,rfl⟩
 · exact CutStrict11.exit_row scalar rfl good checked effect unique inside
     ⟨139,owner,metadata,by simp [CutActor11.Exit]⟩
 · obtain ⟨phase,atIndex⟩ := good.2
   have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
   have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
       (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq]; exact atIndex
   have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
     HazardPhaseCountedCorrection.active_of_step _ _ within _ _ checked
   have holesInside : state.holes⊆soko1_1.initial.holes := by
     rw [atIndex.2.1]
     exact (List.drop_sublist phase _).subset
   have same := UpperHeadCases11.ordinary_effect checked effect metadata (show pushTargets soko1_1.board 114 .east=[115] by decide +kernel)
     (by decide +kernel) holesInside
   subst outcome
   have hero := ActorPrices11.support_of_check 114 state.player .east 113 (by decide +kernel)
     (step_player_clear _ _ _ _ checked).1 (east_support checked metadata)
   have row := of_decide_eq_true (List.all_eq_true.mp price114 _ (List.mem_range.mpr active))
   have ownPrice : 2≤1+scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) 114 115 -
       scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player 114 := by
     rw [hero]
     exact Int.le_of_eq row.symm
   exact OwnedStrict11.owned_stay_bound scalar state .east t good checked 114 115 effect group unique inside owner 2 ownPrice

theorem future_two {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16)
 (hero : state.player=113) (inside : [139,114]⊆state.boulders) :
 2≤energy state final [139,114] outcomes := by
 have good : OwnedCorral11.Good locks region state [139,114] := by
   refine ⟨0,?_,by intro c h; exact h⟩
   rw [hero]
   decide +kernel
 have debt : (groupCertificate 2).groupValue state [139,114]≤-(2:Int) := by
   change weightSum (NetHack.Soko11Hero315.weight _ state.player) [139,114]≤-2
   rw [hero]
   exact of_decide_eq_true (List.all_eq_true.mp debt_pair _ (List.mem_range.mpr active))
 have priced : ∀ state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup → group⊆state.boulders → group.length≤2 →
   step soko1_1.board state dir=some t → Matches state t outcome →
   OwnedCorral11.PaidStep paid group dir t →
   2≤charge (groupCertificate 2).holeWeight group outcome +
     (groupCertificate 2).groupValue t.state (update group outcome) -
     (groupCertificate 2).groupValue state group := by
   intro state dir t outcome group valid unique inside bounded checked effect pays
   exact exit_row valid checked effect unique inside pays
 exact OwnedCorral11.energy_bound closed unique size (groupCertificate 2) 2 priced logged
   (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) [139,114] (by decide) inside rfl good
   reached.holes_sublist.subset debt (goal_value_zero completed _)
#print axioms future_two


theorem survivor_four {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16)
 (hero : state.player=112) (inside : [139,113]⊆state.boulders)
 (survives : endGroup [139] outcomes≠[]) :
 4≤energy state final [139,113] outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have singletonInside : [113]⊆state.boulders := List.Subset.trans (by decide) inside
 have nn := HeroLedger.Logged.energy_nonnegative logged (groupCertificate 2) valid
   [113] (by decide) singletonInside (by decide)
 change 0≤energy state final [113] outcomes at nn
 have split : energy state final [139,113] outcomes =
     energy state final [139] outcomes + energy state final [113] outcomes :=
   HeroLedger.Logged.energy_split logged valid.1 weightAt NetHack.Soko11Hero315.holeWeight [139] [113] (by decide) inside
 have solo := HeroLedger.survivor_energy value NetHack.Soko11Hero315.holeWeight state final 139 outcomes survives
   (goal_value_zero completed _)
 change energy state final [139] outcomes=Int.ofNat (ownPushes [139] outcomes)-value state [139] at solo
 have debt : value state [139]≤-4 := by
   change weightSum (NetHack.Soko11Hero315.weight _ state.player) [139]≤-4
   rw [hero]
   simpa only [weightSum,Int.add_zero] using
     of_decide_eq_true (List.all_eq_true.mp debt139 _ (List.mem_range.mpr active))
 have ownNN : (0:Int)≤Int.ofNat (ownPushes [139] outcomes) := Int.natCast_nonneg _
 omega
#print axioms survivor_four


theorem first_three {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (hero : state.player∈region3 0) (inside : [139,141,113]⊆state.boulders) :
 Nonempty (UpperFirstCut11.FirstCut paid3 state [139,141,113] dirs final pushes moves outcomes) := by
 rcases UpperFirstCut11.first_cut_or_quiet logged [139,141,113] with found|quiet
 · exact found
 · have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have fixed := quiet_fixed quiet rfl valid.1 inside hero reached.holes_sublist.subset [139,113] (by decide)
   have selected := logged.end_subset valid.1 [139,141,113] (by decide) inside
   rw [fixed.2.1] at selected
   have card := List.Nodup.length_le_of_subset (show ([139,141,113] : List Cell).Nodup by decide) selected.2
   have conservation := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   change 3≤final.boulders.length at card
   omega

theorem future_four {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16)
 (hero : state.player=112) (inside : [139,113]⊆state.boulders)
 (blocker : 141∈state.boulders ∨ 140∈state.boulders) :
 4≤energy state final [139,113] outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 by_cases frozen : 140∈state.boulders
 · have pairInside : [139,140]⊆state.boulders := by
     intro c found
     rcases List.mem_cons.mp found with rfl|last
     · exact inside (by simp)
     · have same : c=140 := List.mem_singleton.mp last
       subst c
       exact frozen
   have identity := locked_identity logged (Owner1007.locked_of_check _ [139,140] (by decide +kernel)) pairInside (show 139∈[139,140] by decide)
   exact survivor_four reached logged completed active hero inside (by rw [identity]; decide)
 · have mate : 141∈state.boulders := blocker.resolve_right frozen
   have tripleInside : [139,141,113]⊆state.boulders := by
     intro c found
     rcases List.mem_cons.mp found with rfl|rest
     · exact inside (by simp)
     · rcases List.mem_cons.mp rest with rfl|last
       · exact mate
       · have same : c=113 := List.mem_singleton.mp last
         subst c
         exact inside (by simp)
   have heroInside : state.player∈region3 0 := by rw [hero]; decide +kernel
   obtain ⟨cut⟩ := first_three reached logged completed heroInside tripleInside
   have beforeFacts := quiet_fixed cut.before rfl valid.1 tripleInside heroInside reached.holes_sublist.subset [139,113] (by decide)
   have prior191 := (quiet_fixed cut.before rfl valid.1 tripleInside heroInside reached.holes_sublist.subset [139] (by decide)).2.2
   have prior193 := (quiet_fixed cut.before rfl valid.1 tripleInside heroInside reached.holes_sublist.subset [141] (by decide)).2.2
   have beforeReached := reached.append cut.before.logged.trace
   have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
   have beforeSelected := cut.before.logged.end_subset valid.1 [139,113] (by decide) inside
   rw [beforeFacts.2.2] at beforeSelected
   have beforeTriple := cut.before.logged.end_subset valid.1 [139,141,113] (by decide) tripleInside
   rw [beforeFacts.2.1] at beforeTriple
   obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
   rcases pays with ⟨rfl|rfl,directionEq⟩
   · have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
     have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel)
       (by decide +kernel) beforeReached.holes_sublist.subset
     have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)) := by simpa only [headEq] using cut.headEffect
     have survives := StationaryExit11.after_push_survives cut.before.logged checked effect cut.after valid.1 mate (by decide)
       prior191 (Or.inl prior193) (Owner1007.locked_of_check _ [140,141] (by decide +kernel)) (by decide +kernel)
     have original : endGroup [139] outcomes≠[] := by rw [cut.outcomesEq,headEq]; exact survives
     exact survivor_four reached logged completed active hero inside original
   · have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
     have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata (show pushTargets soko1_1.board 113 .east=[114] by decide +kernel)
       (by decide +kernel) beforeReached.holes_sublist.subset
     have effect : Matches cut.middle cut.actor (.push 113 (.stay 114)) := by simpa only [headEq] using cut.headEffect
     have afterReached := beforeReached.append (Trace.cons checked (Trace.nil cut.actor.state))
     have afterHero : cut.actor.state.player=113 := by rw [effect.2]
     obtain ⟨phase,atIndex⟩ := beforeValid.2
     have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase cut.middle atIndex
     have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
         (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes cut.middle) cut.middle := by rw [←phaseEq]; exact atIndex
     have beforeActive : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes cut.middle<16 :=
       HazardPhaseCountedCorrection.active_of_step _ _ within _ _ checked
     have afterActive : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes cut.actor.state<16 := by
       have holesSame : cut.actor.state.holes=cut.middle.holes := by rw [effect.2]
       simpa only [HazardPhaseCountedCorrection.phaseOf,holesSame] using beforeActive
     have afterActual := step_boulders_nodup _ _ _ _ beforeValid.1 checked
     have selectedAfter := GhostSubset.update_subset _ _ _ effect [139,113] (by decide) beforeSelected.2
     have updateEq : update [139,113] (.push 113 (.stay 114))=[114,139] := by decide
     rw [updateEq] at selectedAfter
     have afterInside : [139,114]⊆cut.actor.state.boulders :=
       List.Subset.trans (by decide) selectedAfter
     have future := future_two afterReached cut.after completed afterActive afterHero afterInside
     have prefixNN := HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 2) valid [139,113] (by decide) inside (by decide)
     change 0≤energy state cut.middle [139,113] cut.beforeOutcomes at prefixNN
     have headCost := CutStrict11.exit_row scalar rfl beforeValid checked effect beforeSelected.1 beforeSelected.2
       ⟨113,by decide,metadata,by simp [CutActor11.Exit]⟩
     change 2≤charge (groupCertificate 2).holeWeight [139,113] (.push 113 (.stay 114))+
       value cut.actor.state (update [139,113] (.push 113 (.stay 114)))-value cut.middle [139,113] at headCost
     have first := energy_append state cut.middle final [139,113] cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
     rw [beforeFacts.2.2] at first
     have second := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final [139,113] cut.headOutcome cut.afterOutcomes
     change energy cut.middle final [139,113] (cut.headOutcome::cut.afterOutcomes)=
       charge (groupCertificate 2).holeWeight [139,113] cut.headOutcome+
       value cut.actor.state (update [139,113] cut.headOutcome)-value cut.middle [139,113]+
       energy cut.actor.state final (update [139,113] cut.headOutcome) cut.afterOutcomes at second
     have perm : (update [139,113] cut.headOutcome).Perm [139,114] := by rw [headEq,updateEq]; decide
     have tailEq := energy_perm perm cut.actor.state final cut.afterOutcomes
     rw [headEq] at second
     rw [headEq] at tailEq
     rw [headEq] at first
     rw [cut.outcomesEq,headEq]
     omega
#print axioms future_four

end Owner1007.EntryFour11
