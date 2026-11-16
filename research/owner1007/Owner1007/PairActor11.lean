import Owner1007.ActorPrices11
namespace Owner1007.PairActor11
open NetHack.Sokoban
open Owner1007.ActorPrices11
def triples : List (Nat × Nat × Nat) := [(138,139,140),(190,191,192),(189,190,191),(191,190,189),(137,138,139),(139,138,137),(111,112,113),(215,216,217)]
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
  (source = 139 ∧ dir = .east) ∨ (source = 191 ∧ dir = .east) ∨
  (source = 190 ∧ (dir = .east ∨ dir = .west)) ∨
  (source = 138 ∧ (dir = .east ∨ dir = .west)) ∨
  (source = 112 ∧ dir = .east) ∨ (source = 216 ∧ dir = .east)
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
    rcases exits with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,dirs⟩ | ⟨rfl,dirs⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have hero := support_of_check 139 state.player .east 138 (by decide +kernel) clear.1 adjacent
      obtain ⟨landing,filled⟩ := ordinary 140 (by decide +kernel) (by decide +kernel)
      refine ⟨140,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
      rw [hero]
      exact price_of_mem phase active 138 139 140 (by decide +kernel)
    · have hero := support_of_check 191 state.player .east 190 (by decide +kernel) clear.1 adjacent
      obtain ⟨landing,filled⟩ := ordinary 192 (by decide +kernel) (by decide +kernel)
      refine ⟨192,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
      rw [hero]
      exact price_of_mem phase active 190 191 192 (by decide +kernel)
    · rcases dirs with rfl | rfl
      · have hero := support_of_check 190 state.player .east 189 (by decide +kernel) clear.1 adjacent
        obtain ⟨landing,filled⟩ := ordinary 191 (by decide +kernel) (by decide +kernel)
        refine ⟨191,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
        rw [hero]
        exact price_of_mem phase active 189 190 191 (by decide +kernel)
      · have hero := support_of_check 190 state.player .west 191 (by decide +kernel) clear.1 adjacent
        obtain ⟨landing,filled⟩ := ordinary 189 (by decide +kernel) (by decide +kernel)
        refine ⟨189,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
        rw [hero]
        exact price_of_mem phase active 191 190 189 (by decide +kernel)
    · rcases dirs with rfl | rfl
      · have hero := support_of_check 138 state.player .east 137 (by decide +kernel) clear.1 adjacent
        obtain ⟨landing,filled⟩ := ordinary 139 (by decide +kernel) (by decide +kernel)
        refine ⟨139,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
        rw [hero]
        exact price_of_mem phase active 137 138 139 (by decide +kernel)
      · have hero := support_of_check 138 state.player .west 139 (by decide +kernel) clear.1 adjacent
        obtain ⟨landing,filled⟩ := ordinary 137 (by decide +kernel) (by decide +kernel)
        refine ⟨137,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
        rw [hero]
        exact price_of_mem phase active 139 138 137 (by decide +kernel)
    · have hero := support_of_check 112 state.player .east 111 (by decide +kernel) clear.1 adjacent
      obtain ⟨landing,filled⟩ := ordinary 113 (by decide +kernel) (by decide +kernel)
      refine ⟨113,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
      rw [hero]
      exact price_of_mem phase active 111 112 113 (by decide +kernel)
    · have hero := support_of_check 216 state.player .east 215 (by decide +kernel) clear.1 adjacent
      obtain ⟨landing,filled⟩ := ordinary 217 (by decide +kernel) (by decide +kernel)
      refine ⟨217,by simpa only [shape,landing],by simpa only [shape,filled],?_⟩
      rw [hero]
      exact price_of_mem phase active 215 216 217 (by decide +kernel)

#print axioms all_prices
#print axioms exit_price
end Owner1007.PairActor11
