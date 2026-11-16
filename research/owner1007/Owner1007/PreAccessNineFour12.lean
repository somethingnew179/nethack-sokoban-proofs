import Owner1007.CageLedger12
import Owner1007.Vertical21223812
import Owner1007.TwoReserves12
import Owner1007.Foreign184UpperFour12
namespace Owner1007.PreAccessNineFour12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev U := CageLedger12.Upper
def locks : Fin 2→List Cell
 |0=>[108,158,159,186,187,210,237,238,213]
 |1=>[108,158,159,186,187,210,211,238,213]
def base : List Cell := [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,236,239,241,242,244,245,246,262,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def region : Fin 2→List Cell |0=>base++[263] |1=>base++[263,237]
def positive (source : Cell) (dir : Dir) : Prop :=
 source=238∧(dir=.east∨dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (positive source dir) := by unfold positive;infer_instance
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210∧dir=.north)∨(source=211∧dir=.north)∨(source=213∧dir=.west)∨(source=238∧dir=.north)∨positive source dir
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem large : ∀ i,2<(locks i).length := by decide +kernel
theorem upper_inside : ∀ i,U⊆locks i := by decide +kernel
theorem hero371 : (371:Cell)∈region 0 := by decide +kernel
theorem foreign_shift : ∀ i,([108,158,159,186,187,184]:List Cell)⊆184::(locks i).erase 210 := by decide +kernel
theorem gate_shift : ∀ i,PriceTrap12Gate.locks 0⊆185::(locks i).erase 211 := by decide +kernel
theorem square_shift : ∀ i,([186,187,212,213]:List Cell)⊆212::(locks i).erase 238 := by decide +kernel
theorem pair_shift : ∀ i,([212,238]:List Cell)⊆212::(locks i).erase 213 := by decide +kernel
theorem gate_hero : (211:Cell)∈PriceTrap12Gate.region 0 := by decide +kernel
theorem pair_hero : (213:Cell)∈Vertical21223812.region 0 := by decide +kernel
theorem paid_outside {source dir} (h : paid source dir) : source∉U := by
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|h
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·obtain ⟨rfl,_⟩:=h;decide +kernel
theorem positive_member {source dir} (h : positive source dir) : source∈([238]:List Cell) := by
 obtain ⟨rfl,_⟩:=h;decide +kernel
theorem positive_price : ∀ source∈([238]:List Cell),∀ dir∈allDirs,positive source dir→
 ∀ dest∈pushTargets soko1_2.board source dir,dest∉soko1_2.initial.holes∧
 (2:Int)≤1+p.boulder dest-p.boulder source := by decide +kernel
theorem upper_bonus : ∀ hero∈([213,238]:List Cell),
 RightEnergy12.cert.bonus hero (NetHack.Sokoban.PatternCorrection.project U)=2 := by decide +kernel
#print axioms matrix
#print axioms upper_bonus
end Owner1007.PreAccessNineFour12
namespace Owner1007.PreAccessNineFour12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem energy_four {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 2}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 4≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays⟩ :=event.split
   have atReached := reached.append first.trace
   have old := first.end_subset actualUnique group gUnique subset
   have nextActual := step_boulders_nodup _ _ _ _ (atReached.boulders_nodup (by decide +kernel)) checked
   have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual _ old.1 old.2
   have nextSubset := GhostSubset.update_subset middle t outcome effect _ old.1 old.2
   have nextReached := atReached.append (Trace.cons checked (Trace.nil t.state))
   have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
   change 0≤ownSlack p group before at nn
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨owner,headPaid⟩:=pays
     have uBefore := List.Subset.trans (upper_inside j) locksHead
     have uMono := update_mono U (endGroup group before) (by decide +kernel) uBefore (.push source ending)
     have uSame : update U (.push source ending)=U := by
       simp only [update,move,if_neg (paid_outside headPaid)]
     rw [uSame] at uMono
     have uNext : U⊆update (endGroup group before) (.push source ending) := uMono
     have uPhysical := List.Subset.trans uNext nextSubset
     have whole : energy p group outcomes=ownSlack p group before+slack p (.push source ending)+
       energy p (update (endGroup group before) (.push source ending)) after := by
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
     have headNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
     change 0≤slack p (.push source ending) at headNN
     rcases headPaid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|headPositive
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 210 .north=[184] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (foreign_shift j)
       change Foreign184UpperFour12.locks 0⊆update (endGroup group before) (.push 210 (.stay 184)) at kept
       have heroNext : t.state.player∈Foreign184UpperFour12.region 0 := by
         rw [matches_hero middle t (.push 210 (.stay 184)) effect]
         exact Foreign184UpperFour12.hero210
       have later := Foreign184UpperFour12.energy_four last nextReached _ nextUnique nextSubset completed heroNext kept
       change 4≤energy p (update (endGroup group before) (.push 210 (.stay 184))) after at later
       omega
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 211 .north=[185] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (gate_shift j)
       have heroNext : t.state.player∈PriceTrap12Gate.region 0 := by
         rw [matches_hero middle t (.push 211 (.stay 185)) effect]
         exact gate_hero
       have later := CageLedger12.gate_owned_nineteen last nextReached _ nextUnique nextSubset heroNext kept
       change 19≤energy p (update (endGroup group before) (.push 211 (.stay 185))) after at later
       omega
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 213 .west=[212] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (pair_shift j)
       have heroNext : t.state.player∈Vertical21223812.region 0 := by
         rw [matches_hero middle t (.push 213 (.stay 212)) effect]
         exact pair_hero
       have pairPhysical := List.Subset.trans kept nextSubset
       have pair := Vertical21223812.owned_energy_two last nextReached [212,238] (by decide +kernel)
         pairPhysical heroNext (fun _ h=>h)
       change 2≤energy p [212,238] after at pair
       have upper := RightEnergy12.raw_group_energy last nextReached U (by decide +kernel) uPhysical completed
       have bonus : RightEnergy12.cert.bonus t.state.player (NetHack.Sokoban.PatternCorrection.project U)=2 := by
         rw [matches_hero middle t (.push 213 (.stay 212)) effect]
         exact upper_bonus 213 (by decide +kernel)
       rw [bonus] at upper
       change 2≤energy p U after at upper
       have both : U++[212,238]⊆update (endGroup group before) (.push 213 (.stay 212)) :=
         List.append_subset.mpr ⟨uNext,kept⟩
       have sum := TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual U [212,238]
         (update (endGroup group before) (.push 213 (.stay 212))) (by decide +kernel) nextUnique nextSubset both
       change energy p U after+energy p [212,238] after≤energy p (update (endGroup group before) (.push 213 (.stay 212))) after at sum
       omega
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 238 .north=[212] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (square_shift j)
       have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update (endGroup group before) (.push 238 (.stay 212))) nextUnique nextSubset
         [186,187,212,213] CageLedger12.locked_middle_square (by decide +kernel) kept
       change debtOf p [186,187,212,213]≤energy p (update (endGroup group before) (.push 238 (.stay 212))) after at later
       have debtBound : (4:Int)≤debtOf p [186,187,212,213] := by decide +kernel
       omega
     · have member := positive_member headPositive
       have price := push_effect_price p soko1_2.initial.holes 2 atReached.holes_sublist.subset
         (positive_price source member dir (Geometry.all_directions dir) headPositive) checked effect
       have upper := RightEnergy12.raw_group_energy last nextReached U (by decide +kernel) uPhysical completed
       have bonus : RightEnergy12.cert.bonus t.state.player (NetHack.Sokoban.PatternCorrection.project U)=2 := by
         rw [matches_hero middle t (.push source ending) effect]
         exact upper_bonus source (List.mem_cons_of_mem 213 member)
       rw [bonus] at upper
       change 2≤energy p U after at upper
       have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual U
         (update (endGroup group before) (.push source ending)) (by decide +kernel) nextUnique uPhysical nextSubset uNext
       change energy p U after≤energy p (update (endGroup group before) (.push source ending)) after at mono
       omega
 · obtain ⟨j,_,kept⟩:=terminal
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept finalInside.2)
   have huge := large j
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms energy_four
end Owner1007.PreAccessNineFour12
