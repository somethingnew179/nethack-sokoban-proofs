import Owner1007.FarUpperBound12
import Owner1007.UpperAfter187Bound12
import Owner1007.Vertical21223812
namespace Owner1007.FarUpperEight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev UA := UpperAfter18712.locks 0
abbrev Pair := Vertical21223812.locks 0
abbrev Ring := RingAfter12.locks true 0
def priceEight (source:Cell) (dir:Dir):Prop :=
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧(8:Int)≤1+p.boulder dest-p.boulder source
instance (source : Cell) (dir : Dir) : Decidable (priceEight source dir) := by unfold priceEight; infer_instance
instance (source : Cell) (dir : Dir) : Decidable (FarUpper12.foreignTwo source dir) := by unfold FarUpper12.foreignTwo; infer_instance
instance (source : Cell) (dir : Dir) : Decidable (FarUpper12.priceSix source dir) := by unfold FarUpper12.priceSix; infer_instance
def ForeignSharp (hero : Cell) (dir : Dir) (source : Cell) : Prop :=
 advance soko1_2.board hero dir=some source →FarUpper12.paid source dir →
 FarUpper12.foreignTwo source dir →(source∉UA ∧source∉Pair) ∨priceEight source dir
instance (hero : Cell) (dir : Dir) (source : Cell) : Decidable (ForeignSharp hero dir source) := by
 unfold ForeignSharp
 infer_instance
theorem foreign_check : ∀ i, ∀ hero∈FarUpper12.region i, ∀ dir∈allDirs, ∀ source∈FarUpper12.sources,
 ForeignSharp hero dir source := by decide +kernel
theorem high_check : ∀ i, ∀ hero∈FarUpper12.region i, ∀ dir∈allDirs, ∀ source∈FarUpper12.sources,
 advance soko1_2.board hero dir=some source →FarUpper12.paid source dir →
 FarUpper12.priceSix source dir →priceEight source dir := by decide +kernel
theorem ua_inside : ∀ i, UA⊆FarUpper12.locks i := by decide +kernel
theorem pair_inside : ∀ i, Pair⊆FarUpper12.locks i := by decide +kernel
theorem ua_hero : ∀ source∈FarUpper12.sources, source∉UA →
 source∈UpperAfter18712.region 0 := by decide +kernel
theorem pair_hero : ∀ source∈FarUpper12.sources, source∉Pair →
 source∈Vertical21223812.region 0 := by decide +kernel

open Owner1007.FarUpper12

theorem ua_pair_four {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (uaHero : state.player∈UpperAfter18712.region 0) (vHero : state.player∈Vertical21223812.region 0)
 (uInside : UA⊆group) (vInside : Pair⊆group) :
 4≤energy p group outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have uActual := List.Subset.trans uInside subset
 have vActual := List.Subset.trans vInside subset
 have u := UpperAfter18712.owned_energy_two UpperAfter18712.matrix logged reached UA
   (by decide +kernel) uActual uaHero (fun _ h=>h)
 have v := Vertical21223812.owned_energy_two logged reached Pair
   (by decide +kernel) vActual vHero (fun _ h=>h)
 change 2≤energy p UA outcomes at u
 change 2≤energy p Pair outcomes at v
 have sum := TwoReserves12.add_le_energy logged Generated.soko1_2_potential_valid actualUnique
   UA Pair group (by decide +kernel) gUnique subset (List.append_subset.mpr ⟨uInside,vInside⟩)
 change energy p UA outcomes+energy p Pair outcomes≤energy p group outcomes at sum
 omega

theorem three_six {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final)
 (uaHero : state.player∈UpperAfter18712.region 0) (vHero : state.player∈Vertical21223812.region 0)
 (rHero : state.player∈TwoReserves12.region true)
 (uInside : UA⊆group) (vInside : Pair⊆group) (rInside : Ring⊆group) :
 6≤energy p group outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have uActual := List.Subset.trans uInside subset
 have vActual := List.Subset.trans vInside subset
 have rActual := List.Subset.trans rInside subset
 have u := UpperAfter18712.owned_energy_two UpperAfter18712.matrix logged reached UA
   (by decide +kernel) uActual uaHero (fun _ h=>h)
 have v := Vertical21223812.owned_energy_two logged reached Pair
   (by decide +kernel) vActual vHero (fun _ h=>h)
 have r := TwoReserves12.ring_two true logged reached Ring
   (by decide +kernel) rActual completed rHero (fun _ h=>h)
 change 2≤energy p UA outcomes at u
 change 2≤energy p Pair outcomes at v
 change 2≤energy p Ring outcomes at r
 have uvInside := List.append_subset.mpr ⟨uInside,vInside⟩
 have uvActual := List.Subset.trans uvInside subset
 have split := logged.energy_split actualUnique p UA Pair (by decide +kernel) uvActual
 have sum := TwoReserves12.add_le_energy logged Generated.soko1_2_potential_valid actualUnique
   (UA++Pair) Ring group (by decide +kernel) gUnique subset (List.append_subset.mpr ⟨uvInside,rInside⟩)
 change energy p (UA++Pair) outcomes+energy p Ring outcomes≤energy p group outcomes at sum
 omega

theorem energy_eight
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 3}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 8≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locksOne,pays⟩ := event.split
   have middleReached := reached.append first.trace
   have middleUnique := middleReached.boulders_nodup (by decide +kernel)
   have oldGroup := first.end_subset actualUnique group gUnique subset
   have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
   have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextSubset := GhostSubset.update_subset middle t outcome effect
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
   have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
   change 0≤ownSlack p group before at prefixNN
   cases outcome with
   | walk target => exact False.elim pays
   | push source ending =>
     obtain ⟨owner,pays⟩ := pays
     obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
     have cases := classification j middle.player heroBefore dir source (sources_paid source dir pays) adjacent pays
     have oneNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
     have keep (dest : Cell) (small : List Cell) (smallShift : small⊆dest::(locks j).erase source) :
        small⊆update (endGroup group before) (.push source (.stay dest)) :=
       CageFour12.shifted_inside (unique j) locksOne owner smallShift
     have reserve (a b : Int) (one : a≤slack p (.push source ending))
       (later : b≤energy p (update (endGroup group before) (.push source ending)) after) :
       a+b≤energy p group outcomes := by
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
       omega

     rcases cases with blocked | gate | quad | cage | far | foreign | expensive
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl,gate⟩ := gate
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 186 .west=[185] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 185 [158,159,185,210] gate
       have heroNext : t.state.player∈PriceTrap12Gate.region 0 := by
         rw [matches_hero middle t (.push 186 (.stay 185)) effect]
         decide +kernel
       have later := CageLedger12.gate_owned_nineteen last nextReached
         (update (endGroup group before) (.push 186 (.stay 185))) nextUnique nextSubset heroNext kept
       change 19≤energy p (update (endGroup group before) (.push 186 (.stay 185))) after at later
       have bound := reserve 0 19 oneNN later
       omega
     · obtain ⟨rfl,rfl,quad⟩ := quad
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 211 (Quad28912.locks 0) quad
       have qActual := List.Subset.trans kept nextSubset
       have heroNext : t.state.player∈Quad28912.region 0 := by
         rw[matches_hero middle t (.push 212 (.stay 211)) effect]
         decide +kernel
       have q := Quad28912.owned_energy_five Quad28912.matrix last nextReached (Quad28912.locks 0)
         (Quad28912.unique 0) qActual heroNext (fun _ h=>h)
       change 5≤energy p (Quad28912.locks 0) after at q
       have uBefore := List.Subset.trans (ua_inside j) locksOne
       have uAfter := update_mono UA (endGroup group before) (by decide +kernel) uBefore (.push 212 (.stay 211))
       simp only[update,move,if_neg (show (212:Cell)∉UA by decide +kernel)] at uAfter
       have uActual := List.Subset.trans uAfter nextSubset
       have heroU : t.state.player∈UpperAfter18712.region 0 := by
         rw[matches_hero middle t (.push 212 (.stay 211)) effect]
         exact ua_hero 212 (by decide +kernel) (by decide +kernel)
       have u := UpperAfter18712.owned_energy_two UpperAfter18712.matrix last nextReached UA
         (by decide +kernel) uActual heroU (fun _ h=>h)
       change 2≤energy p UA after at u
       have sum := TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual
         UA (Quad28912.locks 0) (update (endGroup group before) (.push 212 (.stay 211)))
         (by decide +kernel) nextUnique nextSubset (List.append_subset.mpr ⟨uAfter,kept⟩)
       change energy p UA after+energy p (Quad28912.locks 0) after≤
         energy p (update (endGroup group before) (.push 212 (.stay 211))) after at sum
       have later : 7≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after := by omega
       have bound := reserve 2 7 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := cage
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 262 (Post187Seven12.locks 0) (cage_activation j)
       have heroNext : t.state.player∈Post187Seven12.region 0 := by
         rw [matches_hero middle t (.push 263 (.stay 262)) effect]
         exact cage_hero
       have later := Post187Seven12.owned_energy_seven last nextReached
         (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset cage_credit heroNext kept
       change 7≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
       have one : (2:Int)≤slack p (.push 263 (.stay 262)) := by decide +kernel
       have bound := reserve 2 7 one later
       omega
     · obtain ⟨rfl,rfl⟩ := far
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 289 .west=[288] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have uBefore := List.Subset.trans (ua_inside j) locksOne
       have vBefore := List.Subset.trans (pair_inside j) locksOne
       have uAfter := update_mono UA (endGroup group before) (by decide +kernel) uBefore (.push 289 (.stay 288))
       have vAfter := update_mono Pair (endGroup group before) (by decide +kernel) vBefore (.push 289 (.stay 288))
       simp only[update,move,if_neg (show (289:Cell)∉UA by decide +kernel)] at uAfter
       simp only[update,move,if_neg (show (289:Cell)∉Pair by decide +kernel)] at vAfter
       have heroU : t.state.player∈UpperAfter18712.region 0 := by
         rw[matches_hero middle t (.push 289 (.stay 288)) effect]
         exact ua_hero 289 (by decide +kernel) (by decide +kernel)
       have heroV : t.state.player∈Vertical21223812.region 0 := by
         rw[matches_hero middle t (.push 289 (.stay 288)) effect]
         exact pair_hero 289 (by decide +kernel) (by decide +kernel)
       have later := ua_pair_four last nextReached
         (update (endGroup group before) (.push 289 (.stay 288))) nextUnique nextSubset heroU heroV uAfter vAfter
       have one : (4:Int)≤slack p (.push 289 (.stay 288)) := by decide +kernel
       exact reserve 4 4 one later
     · have sharp := foreign_check j middle.player heroBefore dir (Geometry.all_directions dir)
         source (sources_paid source dir pays) adjacent pays foreign
       obtain ⟨notOldPair,notRing,priced⟩ := foreign
       rcases sharp with ⟨notUA,notNewPair⟩|high
       · have uBefore := List.Subset.trans (ua_inside j) locksOne
         have vBefore := List.Subset.trans (pair_inside j) locksOne
         have rBefore := List.Subset.trans (ringInside j) locksOne
         have uAfter := update_mono UA (endGroup group before) (by decide +kernel) uBefore (.push source ending)
         have vAfter := update_mono Pair (endGroup group before) (by decide +kernel) vBefore (.push source ending)
         have rAfter := update_mono Ring (endGroup group before) (by decide +kernel) rBefore (.push source ending)
         simp only[update,move,if_neg notUA] at uAfter
         simp only[update,move,if_neg notNewPair] at vAfter
         simp only[update,move,if_neg notRing] at rAfter
         have heroU : t.state.player∈UpperAfter18712.region 0 := by
           rw[matches_hero middle t (.push source ending) effect]
           exact ua_hero source (sources_paid source dir pays) notUA
         have heroV : t.state.player∈Vertical21223812.region 0 := by
           rw[matches_hero middle t (.push source ending) effect]
           exact pair_hero source (sources_paid source dir pays) notNewPair
         have heroR : t.state.player∈TwoReserves12.region true := by
           rw[matches_hero middle t (.push source ending) effect]
           exact foreign_ring_hero source (sources_paid source dir pays) notOldPair notRing
         have later := three_six last nextReached
           (update (endGroup group before) (.push source ending)) nextUnique nextSubset completed heroU heroV heroR
           uAfter vAfter rAfter
         have one := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset priced checked effect
         exact reserve 2 6 one later
       · have one := push_effect_price p soko1_2.initial.holes 8 middleReached.holes_sublist.subset high checked effect
         have nn := last.energy_nonnegative Generated.soko1_2_potential_valid (update (endGroup group before) (.push source ending))
         have bound := reserve 8 0 one nn
         omega
     · have high := high_check j middle.player heroBefore dir (Geometry.all_directions dir)
         source (sources_paid source dir pays) adjacent pays expensive
       have one := push_effect_price p soko1_2.initial.holes 8 middleReached.holes_sublist.subset high checked effect
       have bound := event_energy_le Generated.soko1_2_potential_valid group first last (.push source ending)
       simp only[projectedOutcome,if_pos owner] at bound
       rw[shape]
       change slack p (.push source ending)≤energy p group (before++(.push source ending)::after) at bound
       omega
 · obtain ⟨j,hero,locksOne⟩ := terminal
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksOne finalInside.2)
   have size : ∀ j, (locks j).length=12 := by decide +kernel
   rw [size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms energy_eight
end Owner1007.FarUpperEight12


