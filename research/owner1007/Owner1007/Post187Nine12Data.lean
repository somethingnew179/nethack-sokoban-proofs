import Owner1007.Post187SevenMap12
import Owner1007.UpperAfter187Bound12
import Owner1007.VerticalPair12
namespace Owner1007.Post187Nine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def foreign (source : Cell) (dir : Dir) : Prop :=
 (source=239∧dir=.south)∨(source=238∧(dir=.east∨dir=.west))∨(source=213∧(dir=.south∨dir=.east))
instance (source : Cell) (dir : Dir) : Decidable (foreign source dir) := by unfold foreign;infer_instance
def classified (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (Post18712.locks i) source dir∨
 Post18712.gateEvent i source dir∨Post18712.quadEvent i source dir∨
 foreign source dir∨(source=262∧dir=.south)∨(source=161∧dir=.north)∨(source=213∧dir=.north)
instance (i : Fin 10) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by
 unfold classified Post18712.gateEvent Post18712.quadEvent
 infer_instance
def check (i : Fin 8) : Bool :=
 Post18712.paidSources.all fun source=>allDirs.all fun dir=>
 match advance soko1_2.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉Post18712.region (Post18712.basic i)∨¬Post18712.paid source dir∨classified (Post18712.basic i) source dir)
/-- Eight manual footprints, checking one possible support per source/direction;
the existing walking/phase certificate is reused unchanged. -/
theorem checked : ∀i,check i=true := by decide +kernel
theorem classification (i : Fin 8) (hero : Cell) (heroInside : hero∈Post18712.region (Post18712.basic i))
 (dir : Dir) (source : Cell) (member : source∈Post18712.paidSources)
 (adjacent : advance soko1_2.board hero dir=some source) (paid : Post18712.paid source dir) :
 classified (Post18712.basic i) source dir :=by
 have floor := Post187Seven12.floors _ (Post187SevenMap12.post_region _ heroInside)
 have behind := Geometry.reverseCheck_sound soko1_2.board Post187Seven12.reverse hero floor dir source adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp (checked i) source member) dir (Geometry.all_directions dir)
 simp only [check,behind] at row
 rcases of_decide_eq_true row with outside|unpaid|okay
 ·exact False.elim (outside heroInside)
 ·exact False.elim (unpaid paid)
 ·exact okay
theorem foreign_member {source dir} (h : foreign source dir) : source∈([239,238,213]:List Cell) :=by
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;>decide +kernel
theorem foreign_price : ∀ source∈([239,238,213]:List Cell),∀ dir∈allDirs,foreign source dir→
 ∀dest∈pushTargets soko1_2.board source dir,dest∉soko1_2.initial.holes∧
 (2:Int)≤1+p.boulder dest-p.boulder source :=by decide +kernel
theorem foreign_shift : ∀i:Fin 8,∀ source∈([239,238,213]:List Cell),∀ dir∈allDirs,foreign source dir→
 ∀dest∈pushTargets soko1_2.board source dir,
 Post187Seven12.locks (Post187SevenMap12.postIndex (Post18712.basic i))⊆dest::(Post18712.locks (Post18712.basic i)).erase source :=by decide +kernel
theorem foreign_hero : ∀i:Fin 8,∀source∈([239,238,213]:List Cell),
 source∈Post187Seven12.region (Post187SevenMap12.postIndex (Post18712.basic i)) :=by decide +kernel
theorem upper_shift : ∀i:Fin 8,UpperAfter18712.locks 0⊆288::(Post18712.locks (Post18712.basic i)).erase 262 :=by decide +kernel
theorem upper_hero : (262:Cell)∈UpperAfter18712.region 0 :=by decide +kernel
theorem pair_shift : ∀i:Fin 8,VerticalPair12.pair false⊆135::(Post18712.locks (Post18712.basic i)).erase 161 :=by decide +kernel
theorem pair_hero : (161:Cell)∈VerticalPair12.region false 0 :=by decide +kernel
theorem dead_shift : ∀i:Fin 8,([161,187]:List Cell)⊆187::(Post18712.locks (Post18712.basic i)).erase 213 :=by decide +kernel
theorem locked161187 : Locked soko1_2.board [161,187] :=locked_of_check _ _ (by decide +kernel)
theorem terminal_debt : ∀i:Fin 10,(9:Int)≤debtOf p (Post18712.locks i) :=by decide +kernel
#print axioms checked
#print axioms classification
end Owner1007.Post187Nine12
