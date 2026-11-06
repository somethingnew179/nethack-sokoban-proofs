/- Stage-only finite coverage and static-dead-cell certificates. -/
import NetHack.Sokoban41.GeometryChunks18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban

theorem reverse_checked : Geometry.reverseCheck soko4_1.board = true := by decide

theorem reverse (player : Cell) (playerFloor : player ∈ soko4_1.board.floor)
    (direction : Dir) (source : Cell)
    (adjacent : advance soko4_1.board player direction = some source) :
    advance soko4_1.board source direction.opposite = some player :=
  Geometry.reverseCheck_sound soko4_1.board reverse_checked player playerFloor direction source adjacent

theorem checkedDirs_complete (direction : Dir) : direction ∈ checkedDirs := by
  cases direction <;> simp [checkedDirs]

theorem source_order_checked : soko4_1.board.floor.all (sourceOrder.contains) = true := by decide

theorem source_order (source : Cell) (member : source ∈ soko4_1.board.floor) : source ∈ sourceOrder :=
  List.contains_iff_mem.mp (List.all_eq_true.mp source_order_checked source member)

private theorem append_congr {α : Type} {a b c d : List α} (first : a = b) (second : c = d) :
    a ++ c = b ++ d := by rw [first, second]

theorem walks_exact : walkEdges = computedWalks := by
  exact (append_congr walk_player15 (append_congr walk_player16 (append_congr walk_player17 (append_congr walk_player18 (append_congr walk_player23 (append_congr walk_player24 (append_congr walk_player25 (append_congr walk_player29 (append_congr walk_player30 (append_congr walk_player31 (append_congr walk_player32 (append_congr walk_player37 (append_congr walk_player38 (append_congr walk_player39 (append_congr walk_player43 (append_congr walk_player44 (append_congr walk_player45 (append_congr walk_player46 (append_congr walk_player47 (append_congr walk_player48 (append_congr walk_player49 (append_congr walk_player50 (append_congr walk_player51 (append_congr walk_player52 (append_congr walk_player53 (append_congr walk_player57 (append_congr walk_player58 (append_congr walk_player62 (append_congr walk_player66 (append_congr walk_player67 (append_congr walk_player80 (append_congr walk_player85 (append_congr walk_player86 (append_congr walk_player87 (append_congr walk_player88 (append_congr walk_player89 (append_congr walk_player90 (append_congr walk_player92 (append_congr walk_player93 (append_congr walk_player94 (append_congr walk_player95 (append_congr walk_player96 (append_congr walk_player99 (append_congr walk_player100 (append_congr walk_player106 (append_congr walk_player107 (append_congr walk_player108 (append_congr walk_player109 (append_congr walk_player110 (append_congr walk_player114 (append_congr walk_player120 (append_congr walk_player121 (append_congr walk_player122 (append_congr walk_player123 (append_congr walk_player124 (append_congr walk_player128 (append_congr walk_player134 (append_congr walk_player135 (append_congr walk_player136 (append_congr walk_player137 (append_congr walk_player138 (append_congr walk_player142 (append_congr walk_player143 (append_congr walk_player144 (append_congr walk_player145 (append_congr walk_player146 (append_congr walk_player147 (append_congr walk_player148 (append_congr walk_player149 (append_congr walk_player150 (append_congr walk_player151 (append_congr walk_player152 (append_congr walk_player156 (append_congr walk_player157 (rfl : ([] : List WalkEdge) = []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).symm

theorem pushes_exact : pushEdges = computedPushes := by
  exact (append_congr push_source128 (append_congr push_source134 (append_congr push_source135 (append_congr push_source136 (append_congr push_source137 (append_congr push_source138 (append_congr push_source142 (append_congr push_source15 (append_congr push_source16 (append_congr push_source17 (append_congr push_source18 (append_congr push_source143 (append_congr push_source144 (append_congr push_source145 (append_congr push_source146 (append_congr push_source23 (append_congr push_source24 (append_congr push_source25 (append_congr push_source147 (append_congr push_source148 (append_congr push_source149 (append_congr push_source29 (append_congr push_source30 (append_congr push_source31 (append_congr push_source32 (append_congr push_source152 (append_congr push_source156 (append_congr push_source157 (append_congr push_source37 (append_congr push_source38 (append_congr push_source39 (append_congr push_source43 (append_congr push_source44 (append_congr push_source45 (append_congr push_source46 (append_congr push_source47 (append_congr push_source48 (append_congr push_source49 (append_congr push_source50 (append_congr push_source51 (append_congr push_source52 (append_congr push_source53 (append_congr push_source57 (append_congr push_source58 (append_congr push_source62 (append_congr push_source66 (append_congr push_source67 (append_congr push_source80 (append_congr push_source85 (append_congr push_source86 (append_congr push_source87 (append_congr push_source88 (append_congr push_source89 (append_congr push_source90 (append_congr push_source151 (append_congr push_source92 (append_congr push_source93 (append_congr push_source94 (append_congr push_source95 (append_congr push_source96 (append_congr push_source99 (append_congr push_source100 (append_congr push_source106 (append_congr push_source107 (append_congr push_source108 (append_congr push_source109 (append_congr push_source110 (append_congr push_source114 (append_congr push_source150 (append_congr push_source120 (append_congr push_source121 (append_congr push_source122 (append_congr push_source123 (append_congr push_source124 (rfl : ([] : List PushEdge) = []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).symm

theorem walk_coverage (player target : Cell) (direction : Dir)
    (playerFloor : player ∈ soko4_1.board.floor)
    (targetFloor : target ∈ soko4_1.board.floor)
    (adjacent : advance soko4_1.board player direction = some target) :
    (⟨player,target,direction⟩ : WalkEdge) ∈ walkEdges := by
  rw [walks_exact]
  apply List.mem_flatMap.mpr
  refine ⟨player, playerFloor, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨direction, checkedDirs_complete direction, ?_⟩
  have targetTrue : soko4_1.board.floor.contains target = true := List.contains_iff_mem.mpr targetFloor
  simp only [adjacent, targetTrue, ↓reduceIte, List.mem_singleton]

theorem push_coverage (player source : Cell) (direction : Dir) (landing : Cell)
    (playerFloor : player ∈ soko4_1.board.floor)
    (sourceFloor : source ∈ soko4_1.board.floor)
    (adjacent : advance soko4_1.board player direction = some source)
    (landingMember : landing ∈ pushTargets soko4_1.board source direction) :
    ∃ edge ∈ pushEdges, edge.player = player ∧ edge.source = source ∧
      edge.direction = direction ∧ edge.landing = landing := by
  let chosen := computedPushEdge source direction landing
  have member : chosen ∈ computedPushes := by
    apply List.mem_flatMap.mpr
    refine ⟨source, source_order source sourceFloor, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨direction, checkedDirs_complete direction, ?_⟩
    exact List.mem_map.mpr ⟨landing, landingMember, rfl⟩
  have playerEq : chosen.player = player := by
    simp only [chosen, computedPushEdge, reverse player playerFloor direction source adjacent, Option.getD_some]
  exact ⟨chosen, pushes_exact.symm ▸ member, playerEq, rfl, rfl, rfl⟩

end NetHack.Sokoban41
