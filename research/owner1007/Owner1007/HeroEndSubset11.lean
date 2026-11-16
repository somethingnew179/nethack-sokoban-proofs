import Owner1007.HeroEnergySubset11
namespace Owner1007.Hero315Frame11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

theorem end_subset_selected {board state dirs final pushes moves outcomes}
 (logged : Logged board state dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (small big : List Cell)
 (smallUnique : small.Nodup) (bigUnique : big.Nodup)
 (subset : small⊆big) (inside : big⊆state.boulders) :
 endGroup small outcomes⊆endGroup big outcomes := by
 let rest := big.filter (fun c => !decide (c∈small))
 have perm : (small++rest).Perm big := selected_complement small big smallUnique bigUnique subset
 have unique : (small++rest).Nodup := perm.nodup_iff.mpr bigUnique
 have bothInside : small++rest⊆state.boulders := fun _ h => inside (perm.mem_iff.mp h)
 have combined := (endGroup_perm perm outcomes).symm.trans
   (HeroLedger.Logged.end_append_perm logged actualUnique small rest unique bothInside)
 exact fun _ member => combined.mem_iff.mpr (List.mem_append_left _ member)
#print axioms end_subset_selected
end Owner1007.Hero315Frame11
