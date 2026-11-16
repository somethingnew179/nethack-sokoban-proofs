import Owner1007.Post187SevenMap12
import Owner1007.Post187Seven12
import Owner1007.CageFour12
namespace Owner1007.Post187SevenBridge12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem post_seven {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 {i : Fin 10} (hero : state.player∈Post18712.region i) (inside : Post18712.locks i⊆group) :
 7≤energy p group outcomes := by
 exact Post187Seven12.owned_energy_seven logged reached group unique subset
   (i:=Post187SevenMap12.postIndex i) (Post187SevenMap12.post_credit i)
   (Post187SevenMap12.post_region i hero) (List.Subset.trans (Post187SevenMap12.post_inside i) inside)

theorem cage_nine
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .north=some t)
 (effect : Matches middle t (.push 187 (.stay 161)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 10) (lower : 4≤i.val) (upper : i.val<8)
 (inside : Cage10.locks i⊆endGroup group before) :
 9≤energy p group (before++(.push 187 (.stay 161))::after) := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset actualUnique group unique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 187 (.stay 161)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 187 (.stay 161)) effect
   (endGroup group before) old.1 old.2
 have owner : (187:Cell)∈endGroup group before :=
   inside (Cage10.upperInside i (by decide +kernel))
 have kept := CageFour12.shifted_inside (Cage10.unique i) inside owner
   (Post187SevenMap12.cage_inside i lower upper)
 have heroNext : t.state.player∈Post187Seven12.region (Post187SevenMap12.cageIndex i) := by
   rw [matches_hero middle t (.push 187 (.stay 161)) effect]
   exact Post187SevenMap12.cage_hero i
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have later := Post187Seven12.owned_energy_seven last nextReached
   (update (endGroup group before) (.push 187 (.stay 161))) nextUnique nextSubset
   (Post187SevenMap12.cage_credit i) heroNext kept
 change 7≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
 have one : slack p (.push 187 (.stay 161))=2 := by decide +kernel
 have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at nn
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner]
 omega

theorem cage239_nine
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .north=some t)
 (effect : Matches middle t (.push 187 (.stay 161)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 10) (lower : 4≤i.val) (upper : i.val<8)
 (inside : Cage23912.locks i⊆endGroup group before) :
 9≤energy p group (before++(.push 187 (.stay 161))::after) := by
 apply cage_nine first checked effect last reached group unique subset i lower upper
 exact List.Subset.trans (show Cage10.locks i⊆Cage23912.locks i by
   intro c h; exact List.mem_append_left _ h) inside

theorem ring_cage_nine
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .west=some t)
 (effect : Matches middle t (.push 263 (.stay 262)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 3) (inside : RingUpper12.locks i⊆endGroup group before) :
 9≤energy p group (before++(.push 263 (.stay 262))::after) := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset actualUnique group unique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 263 (.stay 262)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 263 (.stay 262)) effect
   (endGroup group before) old.1 old.2
 have owner : (263:Cell)∈endGroup group before := inside (by
   have all : ∀ i : Fin 3, (263:Cell)∈RingUpper12.locks i := by decide +kernel
   exact all i)
 have kept := CageFour12.shifted_inside (RingUpper12.unique i) inside owner
   (Post187SevenMap12.ring_inside i)
 have heroNext : t.state.player∈Post187Seven12.region 0 := by
   rw [matches_hero middle t (.push 263 (.stay 262)) effect]
   exact Post187SevenMap12.ring_hero
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have later := Post187Seven12.owned_energy_seven last nextReached
   (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset
   Post187SevenMap12.ring_credit heroNext kept
 change 7≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
 have one : slack p (.push 263 (.stay 262))=2 := by decide +kernel
 have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at nn
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner]
 omega
#print axioms post_seven
#print axioms cage_nine
#print axioms ring_cage_nine
end Owner1007.Post187SevenBridge12

