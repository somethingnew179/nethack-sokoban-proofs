import Owner1007.Park317Trade12
import Owner1007.DeadCorridor12
import Owner1007.CageLedger12
import Owner1007.OwnedEventsMore12
namespace Owner1007.Park317Cash12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def northCells : List Cell := [345,319,293,292,291]
theorem current_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (cell : Cell) (member : cell∈northCells)
 (park : 317∈state.boulders) (present : cell∈state.boulders)
 (hero : state.player=318) : 2≤energy p [cell] outcomes := by
 by_cases high : cell=345 ∨cell=319
 · rcases Park317Trade12.four_or_survives logged reached cell high park present hero with four|⟨two,_⟩
   ·change 4≤energy p [cell] outcomes at four;omega
   ·exact two
 · have corridor : cell∈([288,289,290,291,292,293,294]:List Cell) := by
     have check : ∀ c∈northCells, c≠345→c≠319→c∈([288,289,290,291,292,293,294]:List Cell) := by decide +kernel
     exact check cell member (fun h=>high (Or.inl h)) (fun h=>high (Or.inr h))
   have survives := DeadCorridor12.trapped_survives logged park reached.holes_sublist.subset cell corridor
   have ledger := survivor_energy p cell outcomes survives
   have initialDebt : (2:Int)≤-p.boulder cell := by
     have check : ∀ c∈northCells, c≠345→c≠319→(2:Int)≤-p.boulder c := by decide +kernel
     exact check cell member (fun h=>high (Or.inl h)) (fun h=>high (Or.inr h))
   have nn : (0:Int)≤(ownPushes [cell] outcomes:Int) := Int.natCast_nonneg _
   simp only[Int.ofNat_eq_natCast] at ledger
   omega

theorem group_five
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .west=some t)
 (effect : Matches middle t (.push 318 (.stay 317)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (cell : Cell) (member : cell∈northCells)
 (owner : (318:Cell)∈endGroup group before)
 (current : cell∈endGroup group before) :
 5≤energy p group (before++(.push 318 (.stay 317))::after) := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have old := first.end_subset actualUnique group unique subset
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 318 (.stay 317)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 318 (.stay 317)) effect
   (endGroup group before) old.1 old.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have boxes : t.state.boulders=317::middle.boulders.erase 318 := by
   simpa only[Matches] using congrArg (fun u : Transition=>u.state.boulders) effect.2
 have park : 317∈t.state.boulders := by rw[boxes];simp
 have different : cell≠318 := by
   have check : ∀ c∈northCells,c≠318 := by decide +kernel
   exact check cell member
 have beforeInside : ([cell]:List Cell)⊆endGroup group before := by
   intro c h
   simpa only[List.mem_singleton.mp h] using current
 have kept := update_mono [cell] (endGroup group before)
   (by simp) beforeInside (.push 318 (.stay 317))
 have outside : (318:Cell)∉([cell]:List Cell) := by simp only[List.mem_singleton];exact Ne.symm different
 simp only[update,move,if_neg outside] at kept
 have cellPresent := (List.Subset.trans kept nextSubset) (show cell∈([cell]:List Cell) by simp)
 have hero : t.state.player=318 := matches_hero middle t (.push 318 (.stay 317)) effect
 have two := current_two last nextReached cell member park cellPresent hero
 have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual
   [cell] (update (endGroup group before) (.push 318 (.stay 317)))
   (by simp) nextUnique (List.Subset.trans kept nextSubset) nextSubset kept
 change energy p [cell] after≤energy p (update (endGroup group before) (.push 318 (.stay 317))) after at mono
 have price : slack p (.push 318 (.stay 317))=3 := by decide +kernel
 have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at nn
 rw[energy_at_split]
 simp only[projectedOutcome,if_pos owner,price]
 omega
#print axioms current_two
#print axioms group_five
end Owner1007.Park317Cash12
