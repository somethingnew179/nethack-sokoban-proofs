import Owner1007.West293Return11
import Owner1007.OtherTrap31811
import Owner1007.QuietGroupFixed11
import Owner1007.GateMarkerSingleton11
import Owner1007.CentralFirst11Geometry
import Owner1007.BeforeCentral31711
import Owner1007.TransportEvents11
namespace Owner1007.BeforeAboveOther11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.ModeC264Mass11 (Other)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def G : List Cell := [266,268,293,317,321]

theorem initial {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (zero : energy soko1_1.initial final Other outcomes=0) (stationary321 : ownPushes [321] outcomes=0)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes)
 (above : boundary.actor.pushSource=some 239 ∧boundary.direction=.south) :
 endGroup G boundary.beforeOutcomes=G := by
 have bound266 := energy_subset (Trace.nil soko1_1.initial) logged [266] Other
   (by decide) (by decide) (by decide) (by decide) (by decide)
 have cheap266 : energy soko1_1.initial final [266] outcomes<2 := by rw [zero] at bound266;omega
 have boundary266 := GateMarkerSingleton11.stationary_before logged boundary 266 (by decide) cheap266
 have gone266 := TightSurvivors11.singleton_nil logged completed Other (by decide) (by decide) (by decide)
   0 (by rw [zero];omega) 266 (by decide) (by decide +kernel)
 have hero213 : boundary.middle.player=213 := by
  have checked : step soko1_1.board boundary.middle .south=some boundary.actor := by simpa only [above.2] using boundary.headChecked
  exact ActorPrices11.support_of_check 239 boundary.middle.player .south 213 (by decide +kernel)
    (step_player_clear _ _ _ _ checked).1 (PairPost11.source_adjacent checked above.1)
 rcases first_cut_or_quiet (paid:=fun _ _=>True) boundary.before.logged G with found|quiet
 ·exfalso
  obtain ⟨first⟩ := found
  have allFixed := QuietGroupFixed11.whole_fixed first.before (by intro c h d;trivial)
  have tagG := no_push_unchanged G first.beforeOutcomes allFixed
  have included := end_subset_selected first.before.logged (by decide) G Other
    (by decide) (by decide) (by decide) (by decide)
  have ownsG : G⊆endGroup Other first.beforeOutcomes := by
   intro c h
   exact included (by rw [tagG];exact h)
  let suffix := Logged.cons boundary.headChecked boundary.headEffect boundary.after
  let last := first.after.append suffix
  have allEffects : first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes)=outcomes := by
   calc
    _=(first.beforeOutcomes++first.headOutcome::first.afterOutcomes)++boundary.headOutcome::boundary.afterOutcomes := by simp only [List.append_assoc,List.cons_append]
    _=boundary.beforeOutcomes++boundary.headOutcome::boundary.afterOutcomes := congrArg (fun before=>before++boundary.headOutcome::boundary.afterOutcomes) first.outcomesEq.symm
    _=outcomes := boundary.outcomesEq.symm
  have zeroWhole : energy soko1_1.initial final Other
      (first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes))=0 := by
   rw [allEffects];exact zero
  have freeze267 (source : Cell) (different : source≠266)
    (metadata : first.actor.pushSource=some source)
    (target : pushTargets soko1_1.board source first.direction=[267]) : False := by
   have headEq := UpperHeadCases11.ordinary_effect first.headChecked first.headEffect metadata target
     (by decide +kernel) first.before.logged.trace.holes_sublist.subset
   have effect : Matches first.middle first.actor (.push source (.stay 267)) := by simpa only [headEq] using first.headEffect
   have fixed := first.before.fixed (by decide :266∈G) (by intro d;trivial)
   have survives := CentralFirst11.stays266 first.before.logged effect last fixed different
   have normalized := allEffects
   rw [headEq] at normalized
   rw [normalized] at survives
   exact survives gone266
  have central_case (source : Cell) (member : source∈CentralFirst11.sources)
    (metadata : first.actor.pushSource=some source) : False := by
   have quietCentral : UpperQuiet11.Quiet CentralFirst11.paid soko1_1.initial G
       first.beforeDirs first.middle first.beforePushes first.beforeMoves first.beforeOutcomes :=
     QuietGroupFixed11.weaken first.before (by intro c d h;trivial)
   have good : OwnedCorral11.Good CentralFirst11.locks CentralFirst11.region soko1_1.initial G :=
     ⟨0,by decide +kernel,by decide⟩
   obtain ⟨i,hero,locks⟩ := Upper216Eight11.quiet_good_any CentralFirst11.closed (by decide +kernel)
     quietCentral (by decide) (by decide) (by decide) good (by simp)
   have factsG := first.before.logged.end_subset (by decide) G (by decide) (by decide)
   have shape := CentralFirst11.head_shape hero (List.Subset.trans locks factsG.2) member first.headChecked metadata
   rcases shape with positive|⟨rfl,west⟩|⟨rfl,west⟩|⟨rfl,north⟩
   ·have facts := first.before.logged.end_subset (by decide) Other (by decide) (by decide)
    have memberG : source∈G := (show CentralFirst11.sources⊆G from by decide) member
    have row := CentralFirst11.exit_row (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.before.logged.trace)
      facts.1 facts.2 first.headChecked first.headEffect ⟨source,ownsG memberG,metadata,positive⟩
    have gap := logged_event_gap_le first.before.logged first.headChecked first.headEffect last Other (by decide) (by decide)
    have bound := Int.le_trans row gap
    change 2≤energy soko1_1.initial final Other
      (first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes)) at bound
    rw [allEffects,zero] at bound
    omega
   ·have target : pushTargets soko1_1.board 293 first.direction=[292] := by rw [west];decide +kernel
    have headEq := UpperHeadCases11.ordinary_effect first.headChecked first.headEffect metadata target
      (by decide +kernel) first.before.logged.trace.holes_sublist.subset
    have checked : step soko1_1.board first.middle .west=some first.actor := by simpa only [west] using first.headChecked
    have effect : Matches first.middle first.actor (.push 293 (.stay 292)) := by simpa only [headEq] using first.headEffect
    have normalized := allEffects
    rw [headEq] at normalized
    have zeroHere : energy soko1_1.initial final Other
        (first.beforeOutcomes++.push 293 (.stay 292)::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes))=0 := by
     rw [normalized];exact zero
    have stationarity : ownPushes [266] (first.beforeOutcomes++.push 293 (.stay 292)::first.afterOutcomes)=0 := by
     have eq := first.outcomesEq
     rw [headEq] at eq
     rw [←eq]
     exact boundary266
    exact West293Return11.impossible first.before.logged checked effect first.after suffix zeroHere
      (List.Subset.trans (by decide :([266,293,317] : List Cell)⊆G) ownsG) stationarity hero213
   ·exact freeze267 268 (by decide) metadata (by rw [west];decide +kernel)
   ·exact freeze267 293 (by decide) metadata (by rw [north];decide +kernel)
  obtain ⟨source,owner,metadata,_⟩ := first.headPaid
  rw [tagG] at owner
  change source∈([266,268,293,317,321] : List Cell) at owner
  simp only [List.mem_cons,List.not_mem_nil,or_false] at owner
  rcases owner with rfl|rfl|rfl|rfl|rfl
  ·exact central_case 266 (by decide) metadata
  ·exact central_case 268 (by decide) metadata
  ·exact central_case 293 (by decide) metadata
  ·have physical317 : 317∈first.middle.boulders :=
     (first.before.logged.end_subset (by decide) G (by decide) (by decide)).2 (by rw [tagG];decide)
   rcases BeforeCentral31711.head_shape physical317 first.headChecked metadata with east|west
   ·have target : pushTargets soko1_1.board 317 first.direction=[318] := by rw [east];decide +kernel
    have headEq := UpperHeadCases11.ordinary_effect first.headChecked first.headEffect metadata target
      (by decide +kernel) first.before.logged.trace.holes_sublist.subset
    have checked : step soko1_1.board first.middle .east=some first.actor := by simpa only [east] using first.headChecked
    have effect : Matches first.middle first.actor (.push 317 (.stay 318)) := by simpa only [headEq] using first.headEffect
    have normalized := allEffects
    rw [headEq] at normalized
    have zeroHere : energy soko1_1.initial final Other
        (first.beforeOutcomes++.push 317 (.stay 318)::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes))=0 := by
     rw [normalized];exact zero
    exact OtherTrap31811.impossible first.before.logged checked effect last completed zeroHere ownsG
   ·have facts := first.before.logged.end_subset (by decide) Other (by decide) (by decide)
    have row := BeforeCentral31711.west_row (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.before.logged.trace)
      facts.1 facts.2 first.headChecked first.headEffect ⟨317,ownsG (by decide),metadata,⟨rfl,west⟩⟩
    have gap := logged_event_gap_le first.before.logged first.headChecked first.headEffect last Other (by decide) (by decide)
    have bound := Int.le_trans row gap
    change 1≤energy soko1_1.initial final Other
      (first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes)) at bound
    rw [allEffects,zero] at bound
    omega
  ·have beforeZero : ownPushes [321] boundary.beforeOutcomes=0 := by
    have whole := stationary321
    rw [boundary.outcomesEq,ownPushes_append] at whole
    omega
   have fixed := first.before.fixed (by decide :321∈G) (by intro d;trivial)
   have tag := no_push_unchanged [321] first.beforeOutcomes fixed
   have pays : OwnedCorral11.PaidStep (fun _ _=>True) (endGroup [321] first.beforeOutcomes) first.direction first.actor :=
    ⟨321,by rw [tag];simp,metadata,True.intro⟩
   have positive := PaidCount11.event_le (paid:=fun _ _=>True) (lastDirs:=first.afterDirs) (last:=first.afterOutcomes)
     first.before.logged first.headEffect [321] pays
   rw [←first.dirsEq,←first.outcomesEq] at positive
   have bound := TransportEvents11.count_le_ownPushes (fun _ _=>True) [321] boundary.beforeDirs boundary.beforeOutcomes
   omega
 ·exact no_push_unchanged G boundary.beforeOutcomes (QuietGroupFixed11.whole_fixed quiet (by intro c h d;trivial))
#print axioms initial
end Owner1007.BeforeAboveOther11
