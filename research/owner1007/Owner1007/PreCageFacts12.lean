import Owner1007.PreCage12
namespace Owner1007.PreCage12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern

theorem tag_sound {n : Nat} (locks region : Fin n → List Cell) (paid : Cell → Dir → Prop)
 (allowed : Fin n → Cell → Dir → Fin n → Cell → Prop)
 [∀ source dir, Decidable (paid source dir)] [∀ i source dir j dest, Decidable (allowed i source dir j dest)]
 (checked : ∀ i, tagPart locks region paid allowed i=true)
 (i : Fin n) (hero : Cell) (heroFloor : hero∈soko1_2.board.floor) (heroInside : hero∈region i)
 (source : Cell) (member : source∈locks i) (dir : Dir)
 (adjacent : advance soko1_2.board hero dir=some source) :
 BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨ TaggedShift locks region allowed i source dir := by
 have behind := Geometry.reverseCheck_sound soko1_2.board reverse_checked hero heroFloor dir source adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp (checked i) source member) dir (Geometry.all_directions dir)
 simp only [tagPart,behind,if_pos heroInside] at row
 exact of_decide_eq_true row

theorem north_tag_sound (i : Fin 10) (hero : Cell) (heroInside : hero∈northRegion i)
 (source : Cell) (member : source∈northLocks i) (dir : Dir)
 (adjacent : advance soko1_2.board hero dir=some source) :
 BlockedPush soko1_2.board (northLocks i) source dir ∨ northPaid source dir ∨
 TaggedShift northLocks northRegion northAllowed i source dir :=
 tag_sound _ _ _ _ north_tagged i hero (north_floor i heroInside) heroInside source member dir adjacent

theorem ring_tag_sound (i : Fin 4) (hero : Cell) (heroInside : hero∈ringRegion i)
 (source : Cell) (member : source∈ringLocks i) (dir : Dir)
 (adjacent : advance soko1_2.board hero dir=some source) :
 BlockedPush soko1_2.board (ringLocks i) source dir ∨ ringPaid source dir ∨
 TaggedShift ringLocks ringRegion ringAllowed i source dir :=
 tag_sound _ _ _ _ ring_tagged i hero (ring_floor i heroInside) heroInside source member dir adjacent

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north_upper_heads : ∀ i, ∀ hero∈northRegion i, ∀ dir∈allDirs, ∀ source∈U,
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (northLocks i) source dir ∨
 (source=187 ∧ dir=.north ∧ northS i=212) := by decide +kernel
theorem ring_upper_heads : ∀ i, ∀ hero∈ringRegion i, ∀ dir∈allDirs, ∀ source∈U,
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (ringLocks i) source dir ∨
 (source=187 ∧ dir=.north ∧ ringS i=212) := by decide +kernel
theorem north_upper_inside : ∀ i, U⊆northLocks i := by decide +kernel
theorem ring_upper_inside : ∀ i, U⊆ringLocks i := by decide +kernel
theorem north_upper_guard : ∀ i hero, hero∈northRegion i → ∀ dir source, source∈U →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (northLocks i) source dir ∨ northPaid source dir := by
 intro i hero _ dir source member _
 exact Or.inr (Or.inr (Or.inl member))
theorem ring_upper_guard : ∀ i hero, hero∈ringRegion i → ∀ dir source, source∈U →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (ringLocks i) source dir ∨ ringPaid source dir := by
 intro i hero _ dir source member _
 exact Or.inr (Or.inr (Or.inl member))

#print axioms north_tag_sound
#print axioms ring_tag_sound
#print axioms north_upper_heads
#print axioms ring_upper_heads
#print axioms north_upper_guard
#print axioms ring_upper_guard
end Owner1007.PreCage12
