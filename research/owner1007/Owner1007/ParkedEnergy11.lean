import Owner1007.Parked18811
import Owner1007.ParkedStrict11
import Owner1007.OwnedCorral11
import Owner1007.Hero315Frame11
import NetHack.Sokoban.Reduction
namespace Owner1007.ParkedEnergy11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem future_energy
    {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
    (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
    (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ state.boulders) (bounded : group.length ≤ 4)
    (good : OwnedCorral11.Good Parked18811.locks Parked18811.region state group) :
    2 ≤ energy state final group outcomes := by
  by_cases bound : 2 ≤ energy state final group outcomes
  · exact bound
  · have cheap : energy state final group outcomes < 2 := by omega
    have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
    have priced : ∀ state dir t outcome group,
      HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
      group.Nodup → group ⊆ state.boulders → group.length ≤ 4 →
      step soko1_1.board state dir = some t → Matches state t outcome →
      OwnedCorral11.PaidStep Parked18811.paid group dir t →
      2 ≤ charge (groupCertificate 4).holeWeight group outcome +
        (groupCertificate 4).groupValue t.state (update group outcome) -
        (groupCertificate 4).groupValue state group := by
      intro state dir t outcome group valid unique inside bounded checked effect pays
      exact ParkedStrict11.exit_row scalar rfl valid checked effect unique inside pays
    have persists := OwnedCorral11.small_energy_good Parked18811.closed Parked18811.unique Parked18811.size
      (groupCertificate 4) 2 priced logged valid group unique inside bounded good reached.holes_sublist.subset cheap
    obtain ⟨i,_,selected⟩ := persists
    have finalSubset := (logged.end_subset valid.1 group unique inside).2
    have actual : Parked18811.locks i ⊆ final.boulders := List.Subset.trans selected finalSubset
    have card := List.Nodup.length_le_of_subset (Parked18811.unique i) actual
    rw [Parked18811.size i] at card
    have conservation := (reached.append logged.trace).conservation
    have empty : final.holes=[] := completed
    rw [empty] at conservation
    change 18+0=final.boulders.length+16 at conservation
    omega
#print axioms future_energy
end Owner1007.ParkedEnergy11
