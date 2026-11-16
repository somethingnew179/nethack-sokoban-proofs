import Owner1007.After290SharpHeads12
import Owner1007.FarT29112
import Owner1007.Ring28812
import Owner1007.Cage239RetainedNine12
import Owner1007.Cage265Nine12
namespace Owner1007.After290Eight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem t_shift : FarT29112.locks 0⊆291::(After29012.locks 1).erase 265 := by decide +kernel
theorem t_hero : (265:Cell)∈FarT29112.region 0 := by decide +kernel
theorem c265_shift : Cage265Retained12.locks (Cage265Retained12.normal 0)⊆262::(After29012.locks 0).erase 263 := by decide +kernel
theorem c265_hero : (263:Cell)∈Cage265Retained12.region (Cage265Retained12.normal 0) := by decide +kernel
theorem c239_shift : Cage239RetainedNine12.locks 0⊆262::(After29012.locks 2).erase 263 := by decide +kernel
theorem far_shift : ∀ i, (CageLedger12.Upper++Ring28812.locks 0)⊆288::(After29012.locks i).erase 289 := by decide +kernel
theorem far_hero : (289:Cell)∈Ring28812.region 0 := by decide +kernel
theorem far_bonus : RightEnergy12.cert.bonus 289 (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by decide +kernel

theorem s_west_shift : ∀ i, (CageLedger12.Upper++Quad28912.locks 0)⊆211::(After29012.locks i).erase 212 := by decide +kernel
theorem s_west_bonus : RightEnergy12.cert.bonus 212 (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by decide +kernel

theorem energy_eight
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 4}
 (hero : state.player∈After29012.region i) (inside : After29012.locks i⊆group) :
 8≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ After29012.matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed After29012.unique logged reached group gUnique subset hero inside with event|terminal
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
     obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
     have cases := After290Strong12.classification j middle.player heroBefore dir source
       (After29012.sources_paid source dir pays) adjacent pays
     have keep (dest : Cell) (small : List Cell) (shift : small⊆dest::(After29012.locks j).erase source) :
        small⊆update (endGroup group before) (.push source (.stay dest)) :=
       CageFour12.shifted_inside (After29012.unique j) locksOne owner shift
     have reserve (a b : Int) (one : a≤slack p (.push source ending))
       (later : b≤energy p (update (endGroup group before) (.push source ending)) after) :
       a+b≤energy p group outcomes := by
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
       omega
     rcases cases with blocked | main | upper | sWest | tSouth | tBack | far | square
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl⟩ := main
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have later : (9:Int)≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after := by
         obtain ⟨v,bound⟩:=j
         have choices:v=0∨v=1∨v=2∨v=3:=by omega
         rcases choices with rfl|rfl|rfl|rfl
         · have kept:=keep 262 (Cage265Retained12.locks (Cage265Retained12.normal 0)) c265_shift
           have heroNext:t.state.player∈Cage265Retained12.region (Cage265Retained12.normal 0):=by
             rw[matches_hero middle t (.push 263 (.stay 262)) effect]
             exact c265_hero
           exact Cage265Nine12.energy_nine last nextReached _ nextUnique nextSubset completed 0 heroNext kept
         · have kept:=keep 262 (Cage21212.locks (Cage212Nine12.normal 0)) (After290Strong12.cage_s212 1 (by decide +kernel))
           have heroNext:t.state.player∈Cage21212.region (Cage212Nine12.normal 0):=by
             rw[matches_hero middle t (.push 263 (.stay 262)) effect]
             exact After290Strong12.cage212hero
           exact Cage212Nine12.energy_nine last nextReached _ nextUnique nextSubset completed 0 heroNext kept
         · have kept:=keep 262 (Cage239RetainedNine12.locks 0) c239_shift
           have heroNext:t.state.player∈Cage239RetainedNine12.region 0:=by
             rw[matches_hero middle t (.push 263 (.stay 262)) effect]
             exact Cage239RetainedNine12.hero263
           exact Cage239RetainedNine12.energy_nine last nextReached _ nextUnique nextSubset completed heroNext kept
         · have kept:=keep 262 (Cage21212.locks (Cage212Nine12.normal 0)) (After290Strong12.cage_s212 3 (by decide +kernel))
           have heroNext:t.state.player∈Cage21212.region (Cage212Nine12.normal 0):=by
             rw[matches_hero middle t (.push 263 (.stay 262)) effect]
             exact After290Strong12.cage212hero
           exact Cage212Nine12.energy_nine last nextReached _ nextUnique nextSubset completed 0 heroNext kept
       have one:(2:Int)≤slack p (.push 263 (.stay 262)):=by decide +kernel
       have bound:=reserve 2 9 one later
       omega
     · obtain ⟨rfl,rfl,odd⟩:=upper
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept:=keep 161 (FarUpper12.locks (After290Strong12.upperIndex j)) (After290Strong12.upper_shift j odd)
       have heroNext:t.state.player∈FarUpper12.region (After290Strong12.upperIndex j):=by
         rw[matches_hero middle t (.push 187 (.stay 161)) effect]
         exact After290Strong12.upper_hero j
       have later:=FarUpper12.energy_six FarUpper12.matrix FarUpper12.classification last nextReached _ nextUnique nextSubset completed heroNext kept
       change 6≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
       have one:(2:Int)≤slack p (.push 187 (.stay 161)):=by decide +kernel
       have bound:=reserve 2 6 one later
       omega
     · obtain ⟨rfl,rfl⟩:=sWest
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept:=keep 211 (CageLedger12.Upper++Quad28912.locks 0) (s_west_shift j)
       have uInside:CageLedger12.Upper⊆update (endGroup group before) (.push 212 (.stay 211)):=by
         intro c h
         exact kept (List.mem_append_left _ h)
       have qInside:Quad28912.locks 0⊆update (endGroup group before) (.push 212 (.stay 211)):=by
         intro c h
         exact kept (List.mem_append_right _ h)
       have uActual:=List.Subset.trans uInside nextSubset
       have qActual:=List.Subset.trans qInside nextSubset
       have uBound:=RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper (by decide +kernel) uActual completed
       have bonus:RightEnergy12.cert.bonus t.state.player
         (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2:=by
         rw[matches_hero middle t (.push 212 (.stay 211)) effect]
         exact s_west_bonus
       rw[bonus] at uBound
       change 2≤energy p CageLedger12.Upper after at uBound
       have heroNext:t.state.player∈Quad28912.region 0:=by
         rw[matches_hero middle t (.push 212 (.stay 211)) effect]
         exact After290Strong12.quad_hero
       have qBound:=Quad28912.owned_energy_five Quad28912.matrix last nextReached (Quad28912.locks 0) (Quad28912.unique 0)
         qActual heroNext (fun _ h=>h)
       change 5≤energy p (Quad28912.locks 0) after at qBound
       have add:=TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual
         CageLedger12.Upper (Quad28912.locks 0) (update (endGroup group before) (.push 212 (.stay 211)))
         (by decide +kernel) nextUnique nextSubset kept
       change energy p CageLedger12.Upper after+energy p (Quad28912.locks 0) after≤
         energy p (update (endGroup group before) (.push 212 (.stay 211))) after at add
       have later:(7:Int)≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after:=by omega
       have one:(2:Int)≤slack p (.push 212 (.stay 211)):=by decide +kernel
       have bound:=reserve 2 7 one later
       omega
     · obtain ⟨rfl,rfl,stage⟩:=tSouth
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have same:j=1:=Fin.ext stage
       subst j
       have kept:=keep 291 (FarT29112.locks 0) t_shift
       have heroNext:t.state.player∈FarT29112.region 0:=by
         rw[matches_hero middle t (.push 265 (.stay 291)) effect]
         exact t_hero
       have later:=FarT29112.energy_six last nextReached _ nextUnique nextSubset completed heroNext kept
       change 6≤energy p (update (endGroup group before) (.push 265 (.stay 291))) after at later
       have one:(2:Int)≤slack p (.push 265 (.stay 291)):=by decide +kernel
       have bound:=reserve 2 6 one later
       omega
     · obtain ⟨rfl,rfl,stage⟩:=tBack
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 239 .south=[265] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have same:j=3:=Fin.ext stage
       subst j
       have kept:=keep 265 (After29012.locks 1) After290Strong12.after_return
       have heroNext:t.state.player∈After29012.region 1:=by
         rw[matches_hero middle t (.push 239 (.stay 265)) effect]
         exact After290Strong12.after_return_hero
       have later:=After29012.energy_six After29012.matrix After29012.classification last nextReached _ nextUnique nextSubset completed heroNext kept
       change 6≤energy p (update (endGroup group before) (.push 239 (.stay 265))) after at later
       have one:(2:Int)≤slack p (.push 239 (.stay 265)):=by decide +kernel
       have bound:=reserve 2 6 one later
       omega
     · obtain ⟨rfl,rfl⟩:=far
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 289 .west=[288] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept:=keep 288 (CageLedger12.Upper++Ring28812.locks 0) (far_shift j)
       have uInside:CageLedger12.Upper⊆update (endGroup group before) (.push 289 (.stay 288)):=by
         intro c h
         exact kept (List.mem_append_left _ h)
       have rInside:Ring28812.locks 0⊆update (endGroup group before) (.push 289 (.stay 288)):=by
         intro c h
         exact kept (List.mem_append_right _ h)
       have uActual:=List.Subset.trans uInside nextSubset
       have rActual:=List.Subset.trans rInside nextSubset
       have uBound:=RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper (by decide +kernel) uActual completed
       have bonus:RightEnergy12.cert.bonus t.state.player
         (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2:=by
         rw[matches_hero middle t (.push 289 (.stay 288)) effect]
         exact far_bonus
       rw[bonus] at uBound
       change 2≤energy p CageLedger12.Upper after at uBound
       have heroNext:t.state.player∈Ring28812.region 0:=by
         rw[matches_hero middle t (.push 289 (.stay 288)) effect]
         exact far_hero
       have rBound:=Ring28812.owned_energy_two last nextReached (Ring28812.locks 0) (Ring28812.unique 0)
         rActual completed heroNext (fun _ h=>h)
       change 2≤energy p (Ring28812.locks 0) after at rBound
       have add:=TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual
         CageLedger12.Upper (Ring28812.locks 0) (update (endGroup group before) (.push 289 (.stay 288)))
         (by decide +kernel) nextUnique nextSubset kept
       change energy p CageLedger12.Upper after+energy p (Ring28812.locks 0) after≤
         energy p (update (endGroup group before) (.push 289 (.stay 288))) after at add
       have later:(4:Int)≤energy p (update (endGroup group before) (.push 289 (.stay 288))) after:=by omega
       have one:(4:Int)≤slack p (.push 289 (.stay 288)):=by decide +kernel
       have bound:=reserve 4 4 one later
       omega
     · obtain ⟨which,shift⟩:=square
       have targets:pushTargets soko1_2.board source dir=[After29012.squareDest source]:=by
         rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide +kernel
       have clear:After29012.squareDest source∉soko1_2.initial.holes:=by
         rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide +kernel
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset targets clear checked effect
       subst ending
       have kept:=keep (After29012.squareDest source) [186,187,212,213] shift
       have later:=last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update (endGroup group before) (.push source (.stay (After29012.squareDest source)))) nextUnique nextSubset
         [186,187,212,213] CageLedger12.locked_middle_square (by decide +kernel) kept
       change debtOf p [186,187,212,213]≤energy p
         (update (endGroup group before) (.push source (.stay (After29012.squareDest source)))) after at later
       have amount:(8:Int)≤debtOf p [186,187,212,213]:=by decide +kernel
       have nn:=logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
       have bound:=reserve 0 (debtOf p [186,187,212,213]) nn later
       omega
 · obtain ⟨j,hero,locksOne⟩:=terminal
   have finalInside:=logged.end_subset actualUnique group gUnique subset
   have count:=List.Nodup.length_le_of_subset (After29012.unique j) (List.Subset.trans locksOne finalInside.2)
   have size:∀ j,(After29012.locks j).length=12:=by decide +kernel
   rw[size j] at count
   have conserved:=(reached.append logged.trace).conservation
   have empty:final.holes=[]:=completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw[empty] at conserved
   simp only[List.length_nil] at conserved
   omega
#print axioms energy_eight
end Owner1007.After290Eight12

