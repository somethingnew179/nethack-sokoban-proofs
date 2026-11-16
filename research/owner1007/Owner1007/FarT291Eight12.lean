import Owner1007.FarT29112
import Owner1007.FarUpperEight12
import Owner1007.After290Eight12
import Owner1007.Cage212Nine12
namespace Owner1007.FarT291Eight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.FarT29112 (locks region sources paid unique)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev U := CageLedger12.Upper
abbrev Pair := Vertical21223812.locks 0
abbrev Ring := RingAfter12.locks true 0
def sharp (i:Fin 1) (source:Cell) (dir:Dir):Prop :=
 BlockedPush soko1_2.board (locks i) source dir∨
 (source=263∧dir=.west)∨(source=187∧dir=.north)∨(source=212∧dir=.west)∨
 (source=291∧dir=.north)∨(source=291∧(dir=.east∨dir=.west∨dir=.south))∨
 (source=289∧dir=.west)
instance (i:Fin 1) (source:Cell) (dir:Dir):Decidable (sharp i source dir):=by unfold sharp;infer_instance
theorem sharp_check:∀ i,∀ hero∈region i,∀ dir∈allDirs,∀ source∈sources,
 advance soko1_2.board hero dir=some source→sharp i source dir:=by decide +kernel
theorem sharp_head (i:Fin 1) (hero:Cell) (heroIn:hero∈region i) (dir source)
 (sourceIn:source∈sources) (adjacent:advance soko1_2.board hero dir=some source):sharp i source dir:=
 sharp_check i hero heroIn dir (Geometry.all_directions dir) source sourceIn adjacent
theorem foreign_price:∀ dir∈([.east,.west,.south]:List Dir),∀ dest∈pushTargets soko1_2.board 291 dir,
 dest∉soko1_2.initial.holes∧(2:Int)≤1+p.boulder dest-p.boulder 291:=by decide +kernel
theorem pair_inside:∀ i,Pair⊆locks i:=by decide +kernel
theorem original_inside:∀ i,U⊆locks i:=by decide +kernel
theorem ring_inside:∀ i,Ring⊆locks i:=by decide +kernel
theorem cage_shift:∀ i,Cage21212.locks (Cage212Nine12.normal 0)⊆262::(locks i).erase 263:=by decide +kernel
theorem cage_hero:(263:Cell)∈Cage21212.region (Cage212Nine12.normal 0):=by decide +kernel
theorem changed_shift:∀ i,FarUpperEight12.UA⊆161::(locks i).erase 187:=by decide +kernel
theorem pair_shift:∀ i,Pair⊆161::(locks i).erase 187:=by decide +kernel
theorem ring_shift:∀ i,Ring⊆161::(locks i).erase 187:=by decide +kernel
theorem raw_bonus291:RightEnergy12.cert.bonus 291 (NetHack.Sokoban.PatternCorrection.project U)=2:=by decide +kernel
theorem raw_bonus289:RightEnergy12.cert.bonus 289 (NetHack.Sokoban.PatternCorrection.project U)=2:=by decide +kernel
theorem quad_shift:∀ i,Quad28912.locks 0⊆211::(locks i).erase 212:=by decide +kernel

theorem original_three_six {state final dirs pushes moves outcomes}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 {history:List Dir}{past pastMoves:Nat}
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (gUnique:group.Nodup) (subset:group⊆state.boulders) (completed:Goal final)
 (bonus:RightEnergy12.cert.bonus state.player (NetHack.Sokoban.PatternCorrection.project U)=2)
 (pairHero:state.player∈Vertical21223812.region 0) (ringHero:state.player∈TwoReserves12.region true)
 (uInside:U⊆group) (vInside:Pair⊆group) (rInside:Ring⊆group):
 6≤energy p group outcomes:=by
 have actualUnique:=reached.boulders_nodup (by decide +kernel)
 have u:=RightEnergy12.raw_group_energy logged reached U (by decide +kernel) (List.Subset.trans uInside subset) completed
 rw[bonus] at u
 have v:=Vertical21223812.owned_energy_two logged reached Pair (by decide +kernel)
   (List.Subset.trans vInside subset) pairHero (fun _ h=>h)
 have r:=TwoReserves12.ring_two true logged reached Ring (by decide +kernel)
   (List.Subset.trans rInside subset) completed ringHero (fun _ h=>h)
 change 2≤energy p U outcomes at u
 change 2≤energy p Pair outcomes at v
 change 2≤energy p Ring outcomes at r
 have uvInside:=List.append_subset.mpr ⟨uInside,vInside⟩
 have split:=logged.energy_split actualUnique p U Pair (by decide +kernel) (List.Subset.trans uvInside subset)
 have sum:=TwoReserves12.add_le_energy logged Generated.soko1_2_potential_valid actualUnique
   (U++Pair) Ring group (by decide +kernel) gUnique subset (List.append_subset.mpr ⟨uvInside,rInside⟩)
 change energy p (U++Pair) outcomes+energy p Ring outcomes≤energy p group outcomes at sum
 omega
theorem energy_eight
 {state final dirs pushes moves outcomes}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 {history:List Dir}{past pastMoves:Nat}
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (gUnique:group.Nodup) (subset:group⊆state.boulders) (completed:Goal final)
 {i:Fin 1}(hero:state.player∈region i) (inside:locks i⊆group):
 8≤energy p group outcomes:=by
 have closed:=PricedCorral11.closed_of_checkExcept _ _ _ _ _ FarT29112.matrix
 have actualUnique:=reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locksOne,pays⟩:=event.split
   have middleReached:=reached.append first.trace
   have middleUnique:=middleReached.boulders_nodup (by decide +kernel)
   have oldGroup:=first.end_subset actualUnique group gUnique subset
   have nextActual:=step_boulders_nodup _ _ _ _ middleUnique checked
   have nextUnique:=GhostSubset.update_unique middle t outcome effect nextActual (endGroup group before) oldGroup.1 oldGroup.2
   have nextSubset:=GhostSubset.update_subset middle t outcome effect (endGroup group before) oldGroup.1 oldGroup.2
   have nextReached:=middleReached.append (Trace.cons checked (Trace.nil t.state))
   have prefixNN:=first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
   change 0≤ownSlack p group before at prefixNN
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨owner,pays⟩:=pays
     obtain ⟨_,adjacent,_⟩:=effect_push_data checked effect
     have cases:=sharp_head j middle.player heroBefore dir source (FarT29112.sources_paid source dir pays) adjacent
     have keep (dest:Cell) (small:List Cell) (shift:small⊆dest::(locks j).erase source):
        small⊆update (endGroup group before) (.push source (.stay dest)):=
       CageFour12.shifted_inside (unique j) locksOne owner shift
     have preserved (small:List Cell) (smallUnique:small.Nodup) (smallInside:small⊆locks j)
       (absent:source∉small):small⊆update (endGroup group before) (.push source ending):=by
       have kept:=update_mono small (endGroup group before) smallUnique (List.Subset.trans smallInside locksOne) (.push source ending)
       simpa only[update,move,if_neg absent] using kept
     have reserve (a b:Int) (one:a≤slack p (.push source ending))
       (later:b≤energy p (update (endGroup group before) (.push source ending)) after):
       a+b≤energy p group outcomes:=by
       rw[shape,energy_at_split]
       simp only[projectedOutcome,if_pos owner]
       omega
     rcases cases with blocked|main|upper|sWest|reset|foreign|far
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl⟩:=main
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept:=keep 262 (Cage21212.locks (Cage212Nine12.normal 0)) (cage_shift j)
       have heroNext:t.state.player∈Cage21212.region (Cage212Nine12.normal 0):=by
         rw[matches_hero middle t (.push 263 (.stay 262)) effect]
         exact cage_hero
       have later:=Cage212Nine12.energy_nine last nextReached _ nextUnique nextSubset completed 0 heroNext kept
       change 9≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
       have one:(2:Int)≤slack p (.push 263 (.stay 262)):=by decide +kernel
       have bound:=reserve 2 9 one later
       omega
     · obtain ⟨rfl,rfl⟩:=upper
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have uInside:=keep 161 FarUpperEight12.UA (changed_shift j)
       have vInside:=keep 161 Pair (pair_shift j)
       have rInside:=keep 161 Ring (ring_shift j)
       have uaHero:t.state.player∈UpperAfter18712.region 0:=by
         rw[matches_hero middle t (.push 187 (.stay 161)) effect]
         decide +kernel
       have vHero:t.state.player∈Vertical21223812.region 0:=by
         rw[matches_hero middle t (.push 187 (.stay 161)) effect]
         decide +kernel
       have rHero:t.state.player∈TwoReserves12.region true:=by
         rw[matches_hero middle t (.push 187 (.stay 161)) effect]
         decide +kernel
       have later:=FarUpperEight12.three_six last nextReached _ nextUnique nextSubset completed
         uaHero vHero rHero uInside vInside rInside
       change 6≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
       have one:(2:Int)≤slack p (.push 187 (.stay 161)):=by decide +kernel
       exact reserve 2 6 one later
     · obtain ⟨rfl,rfl⟩:=sWest
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have qInside:=keep 211 (Quad28912.locks 0) (quad_shift j)
       have uInside:=preserved U (by decide +kernel) (original_inside j) (by decide +kernel)
       have qActual:=List.Subset.trans qInside nextSubset
       have uActual:=List.Subset.trans uInside nextSubset
       have qHero:t.state.player∈Quad28912.region 0:=by
         rw[matches_hero middle t (.push 212 (.stay 211)) effect]
         decide +kernel
       have q:=Quad28912.owned_energy_five Quad28912.matrix last nextReached (Quad28912.locks 0)
         (Quad28912.unique 0) qActual qHero (fun _ h=>h)
       have u:=RightEnergy12.raw_group_energy last nextReached U (by decide +kernel) uActual completed
       have bonus:RightEnergy12.cert.bonus t.state.player (NetHack.Sokoban.PatternCorrection.project U)=2:=by
         rw[matches_hero middle t (.push 212 (.stay 211)) effect]
         exact CageLedger12.upper_bonus 212 (by decide +kernel)
       rw[bonus] at u
       change 2≤energy p U after at u
       change 5≤energy p (Quad28912.locks 0) after at q
       have sum:=TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual U (Quad28912.locks 0)
         (update (endGroup group before) (.push 212 (.stay 211))) (by decide +kernel) nextUnique nextSubset
         (List.append_subset.mpr ⟨uInside,qInside⟩)
       change energy p U after+energy p (Quad28912.locks 0) after≤energy p
         (update (endGroup group before) (.push 212 (.stay 211))) after at sum
       have later:(7:Int)≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after:=by omega
       have one:(2:Int)≤slack p (.push 212 (.stay 211)):=by decide +kernel
       have bound:=reserve 2 7 one later
       omega
     · obtain ⟨rfl,rfl⟩:=reset
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 291 .north=[265] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept:=keep 265 (After29012.locks 1) (FarT29112.return_inside j)
       have heroNext:t.state.player∈After29012.region 1:=by
         rw[matches_hero middle t (.push 291 (.stay 265)) effect]
         exact FarT29112.return_hero
       have later:=After290Eight12.energy_eight last nextReached _ nextUnique nextSubset completed heroNext kept
       change 8≤energy p (update (endGroup group before) (.push 291 (.stay 265))) after at later
       have one:=logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
       have bound:=reserve 0 8 one later
       omega
     · obtain ⟨rfl,choices⟩:=foreign
       have choicesList:dir∈([.east,.west,.south]:List Dir):=by
         simpa only[List.mem_cons,List.not_mem_nil,or_false] using choices
       have uInside:=preserved U (by decide +kernel) (original_inside j) (by decide +kernel)
       have vInside:=preserved Pair (by decide +kernel) (pair_inside j) (by decide +kernel)
       have rInside:=preserved Ring (by decide +kernel) (ring_inside j) (by decide +kernel)
       have bonus:RightEnergy12.cert.bonus t.state.player (NetHack.Sokoban.PatternCorrection.project U)=2:=by
         rw[matches_hero middle t (.push 291 ending) effect]
         exact raw_bonus291
       have vHero:t.state.player∈Vertical21223812.region 0:=by
         rw[matches_hero middle t (.push 291 ending) effect]
         change (291:Cell)∈_
         decide +kernel
       have rHero:t.state.player∈TwoReserves12.region true:=by
         rw[matches_hero middle t (.push 291 ending) effect]
         change (291:Cell)∈_
         decide +kernel
       have later:=original_three_six last nextReached _ nextUnique nextSubset completed bonus vHero rHero uInside vInside rInside
       have one:=push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
         (foreign_price dir choicesList) checked effect
       exact reserve 2 6 one later
     · obtain ⟨rfl,rfl⟩:=far
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 289 .west=[288] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have uInside:=preserved U (by decide +kernel) (original_inside j) (by decide +kernel)
       have vInside:=preserved Pair (by decide +kernel) (pair_inside j) (by decide +kernel)
       have uActual:=List.Subset.trans uInside nextSubset
       have vActual:=List.Subset.trans vInside nextSubset
       have bonus:RightEnergy12.cert.bonus t.state.player (NetHack.Sokoban.PatternCorrection.project U)=2:=by
         rw[matches_hero middle t (.push 289 (.stay 288)) effect]
         exact raw_bonus289
       have u:=RightEnergy12.raw_group_energy last nextReached U (by decide +kernel) uActual completed
       rw[bonus] at u
       have vHero:t.state.player∈Vertical21223812.region 0:=by
         rw[matches_hero middle t (.push 289 (.stay 288)) effect]
         decide +kernel
       have v:=Vertical21223812.owned_energy_two last nextReached Pair (by decide +kernel) vActual vHero (fun _ h=>h)
       change 2≤energy p U after at u
       change 2≤energy p Pair after at v
       have sum:=TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual U Pair
         (update (endGroup group before) (.push 289 (.stay 288))) (by decide +kernel) nextUnique nextSubset
         (List.append_subset.mpr ⟨uInside,vInside⟩)
       change energy p U after+energy p Pair after≤energy p
         (update (endGroup group before) (.push 289 (.stay 288))) after at sum
       have later:(4:Int)≤energy p (update (endGroup group before) (.push 289 (.stay 288))) after:=by omega
       have one:(5:Int)≤slack p (.push 289 (.stay 288)):=by decide +kernel
       have bound:=reserve 5 4 one later
       omega
 · obtain ⟨j,hero,locksOne⟩:=terminal
   have finalInside:=logged.end_subset actualUnique group gUnique subset
   have count:=List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksOne finalInside.2)
   have size:∀ j,(locks j).length=12:=by decide +kernel
   rw[size j] at count
   have conserved:=(reached.append logged.trace).conservation
   have empty:final.holes=[]:=completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw[empty] at conserved
   simp only[List.length_nil] at conserved
   omega
#print axioms energy_eight
end Owner1007.FarT291Eight12
