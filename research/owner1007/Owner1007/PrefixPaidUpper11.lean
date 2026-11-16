import Owner1007.LoggedEventGap11
import Owner1007.UpperLocalPrice11
namespace Owner1007.PrefixPaidUpper11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem prefix_gap_le {beforeDirs middle beforePushes beforeMoves before dir t outcome afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs middle beforePushes beforeMoves before)
 (head : step soko1_1.board middle dir=some t) (effect : Matches middle t outcome)
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆soko1_1.initial.boulders) :
 energy soko1_1.initial middle group before+
 (charge NetHack.Soko11Hero315.holeWeight (endGroup group before) outcome+
 value t.state (update (endGroup group before) outcome)-value middle (endGroup group before))≤
 energy soko1_1.initial final group (before++outcome::after):=by
 have selected:=first.end_subset (by decide) group unique inside
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have afterValid:=(groupCertificate 18).preserved _ _ _ valid head
 have actual:=step_boulders_nodup _ _ _ _ valid.1 head
 have nextUnique:=GhostSubset.update_unique _ _ _ effect actual _ selected.1 selected.2
 have nextInside:=GhostSubset.update_subset _ _ _ effect _ selected.1 selected.2
 have groupBound:=List.Nodup.length_le_of_subset unique inside
 change group.length≤18 at groupBound
 have beforeBound:=endGroup_length_le group before
 have afterBound:=update_length (endGroup group before) outcome
 have afterNN:=HeroLedger.Logged.energy_nonnegative last (groupCertificate 18) afterValid _ nextUnique nextInside (by omega)
 change 0≤energy t.state final (update (endGroup group before) outcome) after at afterNN
 have split:=energy_append soko1_1.initial middle final group before (outcome::after)
 have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight middle t.state final (endGroup group before) outcome after
 change energy middle final (endGroup group before) (outcome::after)=
 charge NetHack.Soko11Hero315.holeWeight (endGroup group before) outcome+
 value t.state (update (endGroup group before) outcome)-value middle (endGroup group before)+
 energy t.state final (update (endGroup group before) outcome) after at one
 omega

theorem plus_two {beforeDirs state beforePushes beforeMoves before dir t outcome afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (source : Cell) (owner : source∈endGroup UpperBudget11.U6 before)
 (metadata : t.pushSource=some source) (paid : UpperLocalPrice11.paid source dir) :
 energy soko1_1.initial state UpperBudget11.U6 before+2≤
 energy soko1_1.initial final UpperBudget11.U6 (before++outcome::after):=by
 have facts:=first.end_subset (by decide) UpperBudget11.U6 (by decide) (by decide)
 have row:=UpperLocalPrice11.exit_row (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace)
  facts.1 facts.2 head effect ⟨source,owner,metadata,paid⟩
 have bound:=prefix_gap_le first head effect last UpperBudget11.U6 (by decide) (by decide)
 omega
#print axioms plus_two
end Owner1007.PrefixPaidUpper11
