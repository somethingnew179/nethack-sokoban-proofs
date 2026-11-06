/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.RowBoundsChunks15
set_option maxRecDepth 10000
namespace NetHack.Sokoban21
open NetHack.Sokoban
def walkGroup16 : List WalkEdge := [⟨206,187,.northEast⟩,⟨206,185,.northWest⟩]
theorem walkGroup16_bound0 : ∀ edge ∈ walkGroup16, WalkBound edge 0 := by
  exact (List.forall_mem_cons.mpr ⟨walk640_0,(List.forall_mem_cons.mpr ⟨walk641_0,(by intro value member; cases member)⟩)⟩)
theorem walkGroup16_bound1 : ∀ edge ∈ walkGroup16, WalkBound edge 1 := by
  exact (List.forall_mem_cons.mpr ⟨walk640_1,(List.forall_mem_cons.mpr ⟨walk641_1,(by intro value member; cases member)⟩)⟩)
theorem walkGroup16_bound2 : ∀ edge ∈ walkGroup16, WalkBound edge 2 := by
  exact (List.forall_mem_cons.mpr ⟨walk640_2,(List.forall_mem_cons.mpr ⟨walk641_2,(by intro value member; cases member)⟩)⟩)
theorem walkGroup16_bound3 : ∀ edge ∈ walkGroup16, WalkBound edge 3 := by
  exact (List.forall_mem_cons.mpr ⟨walk640_3,(List.forall_mem_cons.mpr ⟨walk641_3,(by intro value member; cases member)⟩)⟩)
end NetHack.Sokoban21
