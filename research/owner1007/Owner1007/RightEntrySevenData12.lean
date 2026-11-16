import Owner1007.TaggedFlow12
namespace Owner1007.RightEntrySeven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def fixed : List Cell := [141,168,192,193,218,270]
def locks : Fin 4 → List Cell
 | 0 => [141,168,192,193,218,271,246,270]
 | 1 => [141,168,192,193,218,245,246,270]
 | 2 => [141,168,192,193,218,245,220,270]
 | 3 => [141,168,192,193,218,245,194,270]
def region : Fin 4 → List Cell
 | 0 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,163,164,180,184,185,186,187,189,190,191,206,210,211,212,213,214,215,216,232,236,237,238,239,241,242,258,262,263,264,265,284,288,289,290,291,292,293,294,296,297,310,317,318,319,320,322,336,345,348,370,371,372,373,374,396,397,399,400]
 | 1 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,163,164,180,184,185,186,187,189,190,191,206,210,211,212,213,214,215,216,232,236,237,238,239,241,242,258,262,263,264,265,271,272,284,288,289,290,291,292,293,294,296,297,310,317,318,319,320,322,336,345,348,370,371,372,373,374,396,397,399,400]
 | 2 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,163,164,180,184,185,186,187,189,190,191,206,210,211,212,213,214,215,216,232,236,237,238,239,241,242,246,258,262,263,264,265,271,272,284,288,289,290,291,292,293,294,296,297,310,317,318,319,320,322,336,345,348,370,371,372,373,374,396,397,399,400]
 | 3 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,163,164,180,184,185,186,187,189,190,191,206,210,211,212,213,214,215,216,219,220,232,236,237,238,239,241,242,246,258,262,263,264,265,271,272,284,288,289,290,291,292,293,294,296,297,310,317,318,319,320,322,336,345,348,370,371,372,373,374,396,397,399,400]
def tagS (i : Fin 4) : Cell := if i.val=0 then 271 else 245
def tagT (i : Fin 4) : Cell := if i.val<2 then 246 else if i.val=2 then 220 else 194
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=270 ∧ dir=.north) ∨ (source=193 ∧ dir=.north) ∨
 (source=245 ∧ dir=.north) ∨ (source=245 ∧ dir=.west) ∨ (source=245 ∧ dir=.south)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
def allowed (i : Fin 4) (source : Cell) (dir : Dir) (j : Fin 4) (dest : Cell) : Prop :=
 (i=0 ∧ source=271 ∧ dir=.north ∧ j=1 ∧ dest=245) ∨
 (i=1 ∧ source=246 ∧ dir=.north ∧ j=2 ∧ dest=220) ∨
 (i=2 ∧ source=220 ∧ dir=.north ∧ j=3 ∧ dest=194)
instance (i source dir j dest) : Decidable (allowed i source dir j dest) := by unfold allowed; infer_instance
def matrixNode (i : Fin 4) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir &&
   (locks i).all fun source => decide (advance soko1_2.board hero dir ≠ some source ∨
     BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨
     Corral11.Shift soko1_2.board soko1_2.initial.holes locks region i source dir)
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem sizes : ∀ i, (locks i).length=8 := by decide +kernel
theorem fixed_inside : ∀ i, fixed⊆locks i := by decide +kernel
theorem tagged : ∀ i, PreCage12.tagPart locks region paid allowed i=true := by decide +kernel
theorem floor : ∀ i, region i⊆soko1_2.board.floor := by decide +kernel
theorem tag_inside : ∀ i, tagS i∈locks i ∧ tagT i∈locks i := by decide +kernel
theorem tag_update : ∀ i source dir j dest, allowed i source dir j dest →
 update [tagS i] (.push source (.stay dest))=[tagS j] ∧
 update [tagT i] (.push source (.stay dest))=[tagT j] := by
 intro i source dir j dest h
 rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ <;> decide +kernel
theorem tag_sound (i : Fin 4) (hero : Cell) (heroIn : hero∈region i)
 (source : Cell) (inside : source∈locks i) (dir : Dir)
 (adjacent : advance soko1_2.board hero dir=some source) :
 BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨
 PreCage12.TaggedShift locks region allowed i source dir :=
 PreCage12.tag_sound _ _ _ _ tagged i hero (floor i heroIn) heroIn source inside dir adjacent

theorem fixed_check : ∀ i, ∀ hero∈region i, ∀ dir∈allDirs, ∀ source∈fixed,
 advance soko1_2.board hero dir=some source → BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by decide +kernel
theorem fixed_guard : ∀ i hero, hero∈region i → ∀ dir source, source∈fixed →
 advance soko1_2.board hero dir=some source → BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by
 intro i hero hi dir source inside adjacent
 exact fixed_check i hero hi dir (Geometry.all_directions dir) source inside adjacent

def classified (i : Fin 4) (source : Cell) (dir : Dir) : Prop :=
 (source=270 ∧ dir=.north ∧ [218,244]⊆244::(locks i).erase source) ∨
 (source=193 ∧ dir=.north ∧ i=3) ∨
 (source=245 ∧ dir=.south ∧ i=3) ∨
 (source=245 ∧ dir=.north ∧ [192,193,218,219]⊆219::(locks i).erase source) ∨
 (source=245 ∧ dir=.west ∧ [218,244,270]⊆244::(locks i).erase source)
instance (i source dir) : Decidable (classified i source dir) := by unfold classified; infer_instance
theorem head_check : ∀ i, ∀ hero∈region i, ∀ dir∈allDirs, ∀ source∈locks i,
 advance soko1_2.board hero dir=some source → paid source dir → classified i source dir := by decide +kernel
theorem head_classification (i : Fin 4) (hero : Cell) (hi : hero∈region i) (dir source)
 (inside : source∈locks i) (adjacent : advance soko1_2.board hero dir=some source) (pays : paid source dir) :
 classified i source dir :=
 head_check i hero hi dir (Geometry.all_directions dir) source inside adjacent pays

theorem lockedPair : Locked soko1_2.board [218,244] := locked_of_check _ _ (by decide +kernel)
theorem lockedTriple : Locked soko1_2.board [218,244,270] := locked_of_check _ _ (by decide +kernel)
theorem lockedSquare : Locked soko1_2.board [192,193,218,219] := locked_of_check _ _ (by decide +kernel)
theorem start_right : RightEnergy12.Right⊆locks 0 := by decide +kernel
theorem start_hero : (296:Cell)∈region 0 := by decide +kernel
end Owner1007.RightEntrySeven12

