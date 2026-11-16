import Owner1007.FirstRest18711
import Owner1007.HeroEndSubset11
namespace Owner1007.TransportQuiet11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperQuiet11

theorem Quiet.project {paid state group dirs final pushes moves outcomes}
 (quiet : Quiet paid state group dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (small : List Cell) (smallUnique : small.Nodup) (subset : small⊆group) :
 Quiet paid state small dirs final pushes moves outcomes := by
 induction quiet generalizing small with
 |nil=>exact .nil _ _
 |@cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih=>
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
   have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual group unique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect group unique inside
   have smallInside := List.Subset.trans subset inside
   have nextSmallUnique := GhostSubset.update_unique _ _ _ effect nextActual small smallUnique smallInside
   have one : Logged soko1_1.board state [dir] t.state t.pushCost 1 [outcome] :=
     .cons head effect (.nil _)
   have nextSubset := Hero315Frame11.end_subset_selected one actualUnique small group smallUnique unique subset inside
   change update small outcome⊆update group outcome at nextSubset
   have noSmall : ¬OwnedCorral11.PaidStep paid small dir t := by
     rintro ⟨source,owner,metadata,pays⟩
     exact avoid ⟨source,subset owner,metadata,pays⟩
   exact .cons head effect noSmall (ih nextActual nextUnique nextInside (update small outcome) nextSmallUnique nextSubset)

theorem fill_geometry {state : State} {dir : Dir} {t : Transition} {source hole : Cell}
 (checked : step soko1_1.board state dir=some t)
 (effect : Matches state t (.push source (.fill hole))) :
 hole∈pushTargets soko1_1.board source dir := by
 have sourceEq : t.pushSource=some source := by rw [effect.2.2]
 rcases step_cases_full _ _ _ _ checked with walked|pushed
 · obtain ⟨target,_,_,_,_,shape⟩ := walked
   simp only [shape] at sourceEq
   contradiction
 · obtain ⟨other,result,_,_,_,push,shape⟩ := pushed
   have same : other=source := by simpa only [shape,Option.some.injEq] using sourceEq
   subst other
   have landingEq : result.landing=hole := by
     have eq : t.landing=some hole := by rw [effect.2.2]
     simpa only [shape,Option.some.injEq] using eq
   simpa only [landingEq] using (pushBoulder_spec _ _ _ _ _ push).2

theorem Quiet.transport {paid state group dirs final pushes moves outcomes}
 (quiet : Quiet paid state group dirs final pushes moves outcomes)
 (region : List Cell)
 (closed : ∀source dir dest,source∈region→¬paid source dir→
   dest∈pushTargets soko1_1.board source dir→dest∈region)
 (colored : group⊆region)
 (retain : Bool)
 (noholes : retain=true→∀c∈region,c∉soko1_1.initial.holes)
 (holesInside : state.holes⊆soko1_1.initial.holes) :
 endGroup group outcomes⊆region ∧
 (retain=true→(endGroup group outcomes).length=group.length) := by
 induction quiet with
 |nil=>exact ⟨colored,by intro _;rfl⟩
 |@cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih=>
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
   have nextColored : update group outcome⊆region := by
     cases outcome with
     |walk target=>exact colored
     |push source result=>
       by_cases owner : source∈group
       · have unpaid : ¬paid source dir := by
           intro pays
           have metadata : t.pushSource=some source := by
             cases result with
             |stay target=>rw [effect.2]
             |fill hole=>rw [effect.2.2]
           exact avoid ⟨source,owner,metadata,pays⟩
         have erased : group.erase source⊆region := fun _ h=>colored (List.mem_of_mem_erase h)
         cases result with
         |stay target=>
           have targetInside := closed source dir target (colored owner) unpaid (UpperQuiet11.stay_geometry head effect).2
           simpa only [update,move,if_pos owner,post] using List.cons_subset.mpr ⟨targetInside,erased⟩
         |fill hole=>simpa only [update,move,if_pos owner,post] using erased
       · simpa only [update,move,if_neg owner] using colored
   have sameLength : retain=true→(update group outcome).length=group.length := by
     intro retaining
     cases outcome with
     |walk target=>rfl
     |push source result=>
       by_cases owner : source∈group
       · cases result with
         |stay target=>
           have erased := List.length_erase_of_mem owner
           have positive := List.length_pos_of_mem owner
           simp only [update,move,if_pos owner,post,List.length_cons]
           omega
         |fill hole=>
           have metadata : t.pushSource=some source := by rw [effect.2.2]
           have unpaid : ¬paid source dir := fun pays=>avoid ⟨source,owner,metadata,pays⟩
           have holeRegion := closed source dir hole (colored owner) unpaid (fill_geometry head effect)
           exact False.elim (noholes retaining hole holeRegion (holesInside effect.2.1))
       · simp only [update,move,if_neg owner]
   obtain ⟨endColored,endLength⟩ := ih nextColored nextHoles
   exact ⟨endColored,fun retaining=>(endLength retaining).trans (sameLength retaining)⟩
#print axioms Quiet.project
#print axioms fill_geometry
#print axioms Quiet.transport
end Owner1007.TransportQuiet11
