import Owner1007.TokenPersistence
namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
theorem Logged.end_mono {board state dirs final pushes moves outcomes}
 (logged : Logged board state dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (small big : List Cell)
 (smallUnique : small.Nodup) (inside : small⊆state.boulders) (subset : small⊆big) :
 endGroup small outcomes⊆endGroup big outcomes := by
 induction logged generalizing small big with
 | nil => exact subset
 | @cons state dir t rest final pushes moves outcome outcomes checked effect tail ih =>
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
   have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual small smallUnique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect small smallUnique inside
   exact ih nextActual (update small outcome) (update big outcome) nextUnique nextInside
     (update_mono small big smallUnique subset outcome)
#print axioms Logged.end_mono
end Owner1007.TokenAccounting
