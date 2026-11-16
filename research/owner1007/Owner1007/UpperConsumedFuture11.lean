import Owner1007.OwnedCorralAny11
import Owner1007.UpperCheapConsumed11
import Owner1007.EndGroupMono
import Owner1007.CutEnergy11
namespace Owner1007.UpperConsumedFuture11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.UpperBudget11

theorem future_gone {state final : State} {dirs : List Dir} {pushes moves : Nat} {after : List Outcome}
 (last : Logged soko1_1.board state dirs final pushes moves after)
 (actualUnique : state.boulders.Nodup) (small : List Cell) (unique : small.Nodup) (inside : small⊆state.boulders)
 (before : List Outcome) (subset : small⊆endGroup U6 before)
 (wholeGone : endGroup U6 (before++after)=[]) : endGroup small after=[] := by
 have mono := last.end_mono actualUnique small (endGroup U6 before) unique inside subset
 rw [endGroup_append] at wholeGone
 rw [wholeGone] at mono
 exact List.eq_nil_iff_forall_not_mem.mpr (by intro c member; simpa using mono member)
#print axioms future_gone

theorem future_two {n limit : Nat} {locks region : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (uniqueLocks : ∀ i, (locks i).Nodup) (nonempty : ∀ i, locks i≠[])
 (isExit : ∀source dir, paid source dir → CutActor11.Exit source dir)
 {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤limit)
 (good : OwnedCorral11.Good locks region state group) (consumed : endGroup group outcomes=[]) :
 2≤energy state final group outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have priced : ∀state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup → group⊆state.boulders → group.length≤limit →
   step soko1_1.board state dir=some t → Matches state t outcome →
   OwnedCorral11.PaidStep paid group dir t →
   2≤charge (groupCertificate limit).holeWeight group outcome+
     (groupCertificate limit).groupValue t.state (update group outcome)-(groupCertificate limit).groupValue state group := by
   intro state dir t outcome group valid unique inside bounded checked effect pays
   obtain ⟨source,owner,metadata,pays⟩ := pays
   exact CutStrict11.exit_row scalar rfl valid checked effect unique inside
     ⟨source,owner,metadata,isExit source dir pays⟩
 exact OwnedCorralAny11.energy_if_empty closed uniqueLocks nonempty (groupCertificate limit) 2 priced
   logged valid group unique inside bounded good reached.holes_sublist.subset consumed
#print axioms future_two
end Owner1007.UpperConsumedFuture11
