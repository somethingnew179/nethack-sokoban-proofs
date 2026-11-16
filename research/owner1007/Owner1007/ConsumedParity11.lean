import Owner1007.ConsumedParity11Data
namespace Owner1007.ConsumedParity11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def qValue (_ : State) (group : List Cell) : Int := weightSum q group

theorem one_even {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {dirs final pushes moves outcomes}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (tail : Logged soko1_1.board t.state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (inside : group⊆state.boulders) :
 (charge NetHack.Soko11Hero315.holeWeight group outcome+
   qValue t.state (update group outcome)-qValue state group)%2=0 := by
 cases outcome with
 |walk target=>simp only [charge,update,qValue,Int.zero_add,Int.sub_self];decide
 |push source ending=>
  by_cases owner : source∈group
  ·have sourceCrate := crates_subset valid (inside owner)
   have erased := weightSum_erase q group source owner
   cases ending with
   |stay dest=>
    have target := (UpperQuiet11.stay_geometry head effect).2
    have different := stay_distinct head effect tail completed
    have nextValid := HazardPhases.step_good NetHack.SokobanLinearPhases.Map11.certificate state dir t valid head
    have actualDest : dest∈t.state.boulders := by rw [effect.2];simp
    have destCrate := crates_subset nextValid actualDest
    have numeric := (row source dest dir sourceCrate target different).1 destCrate
    have same : charge NetHack.Soko11Hero315.holeWeight group (.push source (.stay dest))+
      qValue t.state (update group (.push source (.stay dest)))-qValue state group=1+q dest-q source := by
     simp only [charge,update,move,if_pos owner,post,qValue,weightSum]
     omega
    rw [same]
    exact numeric
   |fill hole=>
    have target := TransportQuiet11.fill_geometry head effect
    have different : hole≠source := by
     intro same
     exact boxes_noholes valid source effect.1 (same ▸ effect.2.1)
    obtain ⟨phase,atIndex⟩ := valid.2
    have holesInside : state.holes⊆soko1_1.initial.holes := by rw [atIndex.2.1];exact (List.drop_sublist phase _).subset
    have numeric := (row source hole dir sourceCrate target different).2 (holesInside effect.2.1)
    have same : charge NetHack.Soko11Hero315.holeWeight group (.push source (.fill hole))+
      qValue t.state (update group (.push source (.fill hole)))-qValue state group=
      1-NetHack.Soko11Hero315.holeWeight hole-q source := by
     simp only [charge,update,move,if_pos owner,post,qValue]
     omega
    rw [same]
    exact numeric
  ·cases ending <;> simp only [charge,update,move,if_neg owner,qValue,Int.zero_add,Int.sub_self] <;> decide

theorem aux_even {state dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) :
 (HeroLedger.energy qValue NetHack.Soko11Hero315.holeWeight state final group outcomes)%2=0 := by
 induction logged generalizing group with
 |nil=>simp only [HeroLedger.energy,HeroLedger.charges,endGroup,Int.zero_add,Int.sub_self];decide
 |@cons state dir t rest final pushes moves outcome outcomes head effect tail ih=>
  have nextValid := HazardPhases.step_good NetHack.SokobanLinearPhases.Map11.certificate state dir t valid head
  have actual := step_boulders_nodup _ _ _ _ valid.1 head
  have nextUnique := GhostSubset.update_unique _ _ _ effect actual group unique inside
  have nextInside := GhostSubset.update_subset _ _ _ effect group unique inside
  have nextEven := ih completed nextValid (update group outcome) nextUnique nextInside
  have stepEven := one_even valid head effect tail completed group inside
  have split := OwnedCorral11.energy_cons qValue NetHack.Soko11Hero315.holeWeight state t.state final group outcome outcomes
  rw [split]
  omega

theorem initial_compatible (group : List Cell) (inside : group⊆soko1_1.initial.boulders) :
 (weightSum q group-value soko1_1.initial group)%2=0 := by
 induction group with
 |nil=>simp only [weightSum,value,Int.sub_self];decide
 |cons c rest ih=>
  have first := of_decide_eq_true (List.all_eq_true.mp initial_checked c (inside (by simp)))
  have tail := ih (fun _ h=>inside (List.mem_cons_of_mem _ h))
  change ((q c+weightSum q rest)-(weightAt soko1_1.initial c+weightSum (weightAt soko1_1.initial) rest))%2=0
  change (weightSum q rest-weightSum (weightAt soko1_1.initial) rest)%2=0 at tail
  omega

theorem consumed_even {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆soko1_1.initial.boulders)
 (gone : endGroup group outcomes=[]) :
 (energy soko1_1.initial final group outcomes)%2=0 := by
 have aux := aux_even logged completed NetHack.SokobanLinearPhases.Map11.initial_good group unique inside
 have compatibility := initial_compatible group inside
 change (HeroLedger.charges NetHack.Soko11Hero315.holeWeight group outcomes+
   qValue final (endGroup group outcomes)-qValue soko1_1.initial group)%2=0 at aux
 rw [gone] at aux
 change (HeroLedger.charges NetHack.Soko11Hero315.holeWeight group outcomes+0-weightSum q group)%2=0 at aux
 change (HeroLedger.charges NetHack.Soko11Hero315.holeWeight group outcomes+
   value final (endGroup group outcomes)-value soko1_1.initial group)%2=0
 rw [gone]
 change (HeroLedger.charges NetHack.Soko11Hero315.holeWeight group outcomes+0-value soko1_1.initial group)%2=0
 omega
#print axioms one_even
#print axioms aux_even
#print axioms initial_compatible
#print axioms consumed_even
end Owner1007.ConsumedParity11
