import Owner1007.ActorPrices11
namespace Owner1007.LeftActor11
open NetHack.Sokoban
open Owner1007.ActorPrices11
def triples : List (Nat × Nat × Nat) := [(187,186,185),(213,212,211),(186,185,184),(212,211,210)]
def priceCheck (phase : Nat) : Bool :=
  triples.all fun (hero,source,landing) => decide (price phase hero source landing = 2)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_prices : (List.range 16).all priceCheck = true := by decide +kernel
theorem price_of_mem (phase : Nat) (active : phase < 16) (hero source landing : Nat)
    (member : (hero,source,landing) ∈ triples) : price phase hero source landing = 2 := by
  have row := List.all_eq_true.mp all_prices phase (List.mem_range.mpr active)
  exact of_decide_eq_true (List.all_eq_true.mp row (hero,source,landing) member)
def Exit (source : Cell) (dir : Dir) : Prop :=
  (source = 185 ∨ source = 186 ∨ source = 211 ∨ source = 212) ∧ dir = .west
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
    rcases exits with ⟨sourceChoice,rfl⟩
    rcases sourceChoice with rfl | rfl | rfl | rfl
    · have hero := support_of_check 185 state.player .west 186 (by decide +kernel) clear.1 adjacent
      obtain ⟨landing,filled⟩ := ordinary 184 (by decide +kernel) (by decide +kernel)
      refine ⟨184,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
      rw [hero]
      exact price_of_mem phase active 186 185 184 (by decide +kernel)
    · have hero := support_of_check 186 state.player .west 187 (by decide +kernel) clear.1 adjacent
      obtain ⟨landing,filled⟩ := ordinary 185 (by decide +kernel) (by decide +kernel)
      refine ⟨185,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
      rw [hero]
      exact price_of_mem phase active 187 186 185 (by decide +kernel)
    · have hero := support_of_check 211 state.player .west 212 (by decide +kernel) clear.1 adjacent
      obtain ⟨landing,filled⟩ := ordinary 210 (by decide +kernel) (by decide +kernel)
      refine ⟨210,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
      rw [hero]
      exact price_of_mem phase active 212 211 210 (by decide +kernel)
    · have hero := support_of_check 212 state.player .west 213 (by decide +kernel) clear.1 adjacent
      obtain ⟨landing,filled⟩ := ordinary 211 (by decide +kernel) (by decide +kernel)
      refine ⟨211,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
      rw [hero]
      exact price_of_mem phase active 213 212 211 (by decide +kernel)

#print axioms all_prices
#print axioms exit_price
end Owner1007.LeftActor11
