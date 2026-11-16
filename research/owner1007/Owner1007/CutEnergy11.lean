import Owner1007.CutStrict11
import Owner1007.OwnedCorral11
import Owner1007.Hero315Frame11
import Owner1007.UpperZero11
import Owner1007.WestAfter11
import NetHack.Sokoban.Reduction
namespace Owner1007.CutEnergy11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem future_energy {n k : Nat} {locks region : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
    (uniqueLocks : ∀ i, (locks i).Nodup) (size : ∀ i, (locks i).length=k) (large : 2<k)
    (isExit : ∀ source dir, paid source dir → CutActor11.Exit source dir)
    {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
    (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
    (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ state.boulders) (bounded : group.length ≤ k)
    (good : OwnedCorral11.Good locks region state group) :
    2 ≤ energy state final group outcomes := by
  by_cases bound : 2 ≤ energy state final group outcomes
  · exact bound
  · have cheap : energy state final group outcomes < 2 := by omega
    have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
    have priced : ∀ state dir t outcome group,
      HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
      group.Nodup → group ⊆ state.boulders → group.length ≤ k →
      step soko1_1.board state dir = some t → Matches state t outcome →
      OwnedCorral11.PaidStep paid group dir t →
      2 ≤ charge (groupCertificate k).holeWeight group outcome +
        (groupCertificate k).groupValue t.state (update group outcome) -
        (groupCertificate k).groupValue state group := by
      intro state dir t outcome group valid unique inside bounded checked effect pays
      obtain ⟨source,owner,metadata,pays⟩ := pays
      exact CutStrict11.exit_row scalar rfl valid checked effect unique inside
        ⟨source,owner,metadata,isExit source dir pays⟩
    have persists := OwnedCorral11.small_energy_good closed uniqueLocks size
      (groupCertificate k) 2 priced logged valid group unique inside bounded good reached.holes_sublist.subset cheap
    obtain ⟨i,_,selected⟩ := persists
    have finalSubset := (logged.end_subset valid.1 group unique inside).2
    have actual : locks i ⊆ final.boulders := List.Subset.trans selected finalSubset
    have card := List.Nodup.length_le_of_subset (uniqueLocks i) actual
    rw [size i] at card
    have conservation := (reached.append logged.trace).conservation
    have empty : final.holes=[] := completed
    rw [empty] at conservation
    change 18+0=final.boulders.length+16 at conservation
    omega

theorem upper_paid (source : Cell) (dir : Dir) (paid : UpperZero11.paid source dir) : CutActor11.Exit source dir := by
 rcases paid with h|h|h|h|h|h <;> simp_all [CutActor11.Exit]
theorem west_paid (source : Cell) (dir : Dir) (paid : WestAfter11.paid source dir) : CutActor11.Exit source dir := by
 rcases paid with h|h|h|h <;> simp_all [CutActor11.Exit]

#print axioms future_energy
#print axioms upper_paid
#print axioms west_paid
end Owner1007.CutEnergy11
