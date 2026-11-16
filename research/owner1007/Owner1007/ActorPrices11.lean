import Owner1007.Corral11
import NetHack.Soko11Hero315.Reader

namespace Owner1007.ActorPrices11
open NetHack.Sokoban

def price (phase hero source landing : Nat) : Int :=
  1 + NetHack.Soko11Hero315.weight phase source landing -
    NetHack.Soko11Hero315.weight phase hero source

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def priceCheck (phase : Nat) : Bool :=
  decide (price phase 189 188 187 = 2) &&
  decide (price phase 214 213 212 = 2) &&
  decide (price phase 215 216 217 = 2)
theorem all_prices : (List.range 16).all priceCheck = true := by decide +kernel

theorem prices (phase : Nat) (active : phase < 16) :
    price phase 189 188 187 = 2 ∧ price phase 214 213 212 = 2 ∧
      price phase 215 216 217 = 2 := by
  have checked := List.all_eq_true.mp all_prices phase (List.mem_range.mpr active)
  exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).1,
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).2,
    of_decide_eq_true (Bool.and_eq_true_iff.mp checked).2⟩

def supportCheck (source landing : Cell) (dir : Dir) : Bool :=
  soko1_1.board.floor.all fun hero =>
    decide (advance soko1_1.board hero dir ≠ some source ∨ hero = landing)

theorem support_of_check (source hero : Cell) (dir : Dir) (expected : Cell)
    (checked : supportCheck source expected dir = true) (floor : hero ∈ soko1_1.board.floor)
    (adjacent : advance soko1_1.board hero dir = some source) : hero = expected := by
  have entry := of_decide_eq_true (List.all_eq_true.mp checked hero floor)
  exact entry.resolve_left (fun different => different adjacent)

theorem support188 : supportCheck 188 189 .west = true := by decide +kernel
theorem support213 : supportCheck 213 214 .west = true := by decide +kernel
theorem support216 : supportCheck 216 215 .east = true := by decide +kernel

def Exit (source : Cell) (dir : Dir) : Prop :=
  (source = 188 ∧ dir = .west) ∨ (source = 213 ∧ dir = .west) ∨ (source = 216 ∧ dir = .east)

/-- Price of the actor only; this does not assert an extra full-map scalar charge. -/
theorem exit_price {state : State} {dir : Dir} {t : Transition} {source : Cell}
    (checked : step soko1_1.board state dir = some t)
    (sourceEq : t.pushSource = some source) (exits : Exit source dir)
    (holesInside : state.holes ⊆ soko1_1.initial.holes)
    (phase : Nat) (active : phase < 16) :
    ∃ landing, t.landing = some landing ∧ t.filled = none ∧
      price phase state.player source landing = 2 := by
  have clear := step_player_clear _ _ _ _ checked
  rcases step_cases_full _ _ _ _ checked with walked | pushed
  · obtain ⟨target, _, _, _, _, shape⟩ := walked
    simp only [shape] at sourceEq
    contradiction
  · obtain ⟨other, result, adjacent, _, _, push, shape⟩ := pushed
    have same : other = source := by simpa only [shape, Option.some.injEq] using sourceEq
    subst other
    have spec := pushBoulder_spec _ _ _ _ _ push
    have ordinary (landing : Cell) (targets : pushTargets soko1_1.board source dir = [landing])
        (notHole : landing ∉ soko1_1.initial.holes) :
        result.landing = landing ∧ result.filled = none := by
      have landed : result.landing = landing := by simpa only [targets, List.mem_singleton] using spec.2
      refine ⟨landed, ?_⟩
      rcases spec.1 with stay | fill
      · exact stay.1
      · exact False.elim (notHole (holesInside (landed ▸ fill.2.1)))
    rcases exits with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hero := support_of_check 188 state.player .west 189 support188 clear.1 adjacent
      obtain ⟨landing, filled⟩ := ordinary 187 (by decide +kernel) (by decide +kernel)
      refine ⟨187, by simpa only [shape, landing], by simpa only [shape, filled], ?_⟩
      rw [hero]
      exact (prices phase active).1
    · have hero := support_of_check 213 state.player .west 214 support213 clear.1 adjacent
      obtain ⟨landing, filled⟩ := ordinary 212 (by decide +kernel) (by decide +kernel)
      refine ⟨212, by simpa only [shape, landing], by simpa only [shape, filled], ?_⟩
      rw [hero]
      exact (prices phase active).2.1
    · have hero := support_of_check 216 state.player .east 215 support216 clear.1 adjacent
      obtain ⟨landing, filled⟩ := ordinary 217 (by decide +kernel) (by decide +kernel)
      refine ⟨217, by simpa only [shape, landing], by simpa only [shape, filled], ?_⟩
      rw [hero]
      exact (prices phase active).2.2

#print axioms all_prices
#print axioms exit_price
end Owner1007.ActorPrices11
