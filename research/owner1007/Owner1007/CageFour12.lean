import Owner1007.Cage10
import Owner1007.CageLedger12
import Owner1007.VerticalPair12
import Owner1007.OwnedEventsMore12
namespace Owner1007.CageFour12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem blocked_impossible {state dir t source ending K}
    (inside : K ⊆ state.boulders) (checked : step soko1_2.board state dir = some t)
    (effect : Matches state t (.push source ending))
    (blocked : BlockedPush soko1_2.board K source dir) : False := by
  obtain ⟨result,_,push⟩ := effect_push_data checked effect
  have first := push_first_clear soko1_2.board state source dir result push
  rcases blocked with diagonal | blocked
  · simp only [first.1] at diagonal
    contradiction
  · obtain ⟨dest,next,floor,door,empty⟩ := first.2
    simp only [next] at blocked
    rcases blocked with wall | badDoor | box
    · exact wall floor
    · exact door badDoor
    · exact empty (inside box)

theorem shifted_inside {K group small : List Cell} {source dest : Cell}
    (unique : K.Nodup) (inside : K ⊆ group) (owner : source ∈ group)
    (shifted : small ⊆ dest :: K.erase source) :
    small ⊆ update group (.push source (.stay dest)) := by
  have erased := GhostSubset.erase_subset inside unique source
  simp only [update,move,if_pos owner,post]
  exact List.Subset.trans shifted (List.cons_subset_cons dest erased)

theorem energy_four {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final) {i : Fin 10}
    (hero : state.player ∈ Cage10.region i) (inside : Cage10.locks i ⊆ group) :
    4 ≤ energy p group outcomes := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ Cage10.matrix
  have initialUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed Cage10.unique logged reached group unique subset hero inside with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locks,pays⟩ := event.split
    have middleReached := reached.append first.trace
    have middleUnique := middleReached.boulders_nodup (by decide +kernel)
    have oldGroup := first.end_subset initialUnique group unique subset
    have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
    have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
      (endGroup group before) oldGroup.1 oldGroup.2
    have nextSubset := GhostSubset.update_subset middle t outcome effect
      (endGroup group before) oldGroup.1 oldGroup.2
    have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
    have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
    by_cases basic : j.val < 8
    · cases outcome with
      | walk target => exact False.elim pays
      | push source ending =>
        obtain ⟨owner,paid⟩ := pays
        obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
        let b : Fin 8 := ⟨j.val,basic⟩
        have same : Cage10.basic b = j := Fin.ext rfl
        have classified := Cage10.classification b middle.player (by simpa only [same] using heroBefore)
          dir source (Cage10.paid_sources source dir paid) adjacent paid
        rw [same] at classified
        have oneNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
        have reserve (a b : Int) (one : a ≤ slack p (.push source ending))
            (later : b ≤ energy p (update (endGroup group before) (.push source ending)) after) :
            a+b ≤ energy p group outcomes := by
          rw [shape,energy_at_split]
          simp only [projectedOutcome,if_pos owner]
          change 0 ≤ ownSlack p group before at prefixNN
          omega
        have lockedBound (dest : Cell)
            (targets : pushTargets soko1_2.board source dir = [dest])
            (clear : dest ∉ soko1_2.initial.holes)
            (small : List Cell) (smallUnique : small.Nodup) (locked : Locked soko1_2.board small)
            (shift : small ⊆ dest :: (Cage10.locks j).erase source) :
            debtOf p small ≤ energy p (update (endGroup group before) (.push source ending)) after := by
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            targets clear checked effect
          subst ending
          have kept := shifted_inside (Cage10.unique j) locks owner shift
          exact last.locked_group_energy Generated.soko1_2_potential_valid nextActual
            (update (endGroup group before) (.push source (.stay dest))) nextUnique nextSubset
            small locked smallUnique kept
        rcases classified with blocked | upperEvent | gateEvent | squareEvent | priceTwo
        · exact False.elim (blocked_impossible (List.Subset.trans locks oldGroup.2) checked effect blocked)
        · obtain ⟨rfl,rfl,pairInside⟩ := upperEvent
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            (show pushTargets soko1_2.board 187 .north = [161] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          have shifted : ([186,212] : List Cell) ⊆ 161 :: (Cage10.locks j).erase 187 := by
            intro c found
            apply List.mem_cons_of_mem
            have different : c ≠ 187 := by intro same; subst c; simp at found
            exact (List.mem_erase_of_ne different).mpr (pairInside found)
          have kept := shifted_inside (Cage10.unique j) locks owner shifted
          have newHero : t.state.player ∈ VerticalPair12.region false 0 := by
            rw [matches_hero middle t (.push 187 (.stay 161)) effect]
            decide +kernel
          have later := VerticalPair12.owned_energy_two false last nextReached
            (update (endGroup group before) (.push 187 (.stay 161))) nextUnique nextSubset newHero kept
          change 2 ≤ energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
          have one : (2 : Int) ≤ slack p (.push 187 (.stay 161)) := by decide +kernel
          exact reserve 2 2 one later
        · obtain ⟨rfl,rfl,gateOrSquare⟩ := gateEvent
          rcases gateOrSquare with gate | square
          · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              (show pushTargets soko1_2.board 211 .north = [185] by decide +kernel)
              (by decide +kernel) checked effect
            subst ending
            have kept := shifted_inside (Cage10.unique j) locks owner gate
            have newHero : t.state.player ∈ PriceTrap12Gate.region 0 := by
              rw [matches_hero middle t (.push 211 (.stay 185)) effect]
              decide +kernel
            have later := CageLedger12.gate_owned_nineteen last nextReached
              (update (endGroup group before) (.push 211 (.stay 185))) nextUnique nextSubset newHero kept
            change 19 ≤ energy p (update (endGroup group before) (.push 211 (.stay 185))) after at later
            have bound := reserve 0 19 oneNN later
            omega
          · have later := lockedBound 185 (by decide +kernel) (by decide +kernel)
              [158,159,184,185] (by decide +kernel) CageLedger12.locked_upper_square square
            have amount : (4 : Int) ≤ debtOf p [158,159,184,185] := by decide +kernel
            have bound := reserve 0 (debtOf p [158,159,184,185]) oneNN later
            omega
        · obtain ⟨which,shifted⟩ := squareEvent
          have targets : pushTargets soko1_2.board source dir = [212] := by
            rcases which with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel
          have later := lockedBound 212 targets (by decide +kernel)
            [186,187,212,213] (by decide +kernel) CageLedger12.locked_middle_square shifted
          have amount : (4 : Int) ≤ debtOf p [186,187,212,213] := by decide +kernel
          have bound := reserve 0 (debtOf p [186,187,212,213]) oneNN later
          omega
        · obtain ⟨notUpper,priced⟩ := priceTwo
          have one := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset priced checked effect
          have upperBefore : CageLedger12.Upper ⊆ endGroup group before :=
            List.Subset.trans (Cage10.upperInside j) locks
          have upperAfter := update_mono CageLedger12.Upper (endGroup group before)
            (by decide +kernel) upperBefore (.push source ending)
          change source ∉ CageLedger12.Upper at notUpper
          simp only [update,move,if_neg notUpper] at upperAfter
          have actualUpper := List.Subset.trans upperAfter nextSubset
          have upperBound := RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper
            (by decide +kernel) actualUpper completed
          have allSources := Cage10.paid_sources source dir paid
          have outsideSources : source ∈ ([213,212,237,211,210,184,238,262,236] : List Cell) := by
            exact (List.mem_append.mp allSources).resolve_left notUpper
          rw [matches_hero middle t (.push source ending) effect] at upperBound
          simp only [nextHero] at upperBound
          rw [CageLedger12.upper_bonus source outsideSources] at upperBound
          change 2 ≤ energy p CageLedger12.Upper after at upperBound
          have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual
            CageLedger12.Upper (update (endGroup group before) (.push source ending))
            (by decide +kernel) nextUnique actualUpper nextSubset upperAfter
          have later : (2 : Int) ≤ energy p (update (endGroup group before) (.push source ending)) after :=
            Int.le_trans upperBound mono
          exact reserve 2 2 one later
    · have large : 8 ≤ j.val := by omega
      have pair := Cage10.badPair j large
      have rest : Logged soko1_2.board middle (dir::afterDirs) final (t.pushCost+afterPushes) (1+afterMoves)
          (outcome::after) := .cons checked effect last
      rcases pair with pair | pair
      · have later := rest.locked_group_energy Generated.soko1_2_potential_valid middleUnique
          (endGroup group before) oldGroup.1 oldGroup.2
          [210,236] CageLedger12.locked_210236 (by decide +kernel) (List.Subset.trans pair locks)
        change debtOf p [210,236] ≤ energy p (endGroup group before) (outcome::after) at later
        have amount : (4 : Int) ≤ debtOf p [210,236] := by decide +kernel
        rw [shape,TokenAccounting.energy_append]
        change 0 ≤ ownSlack p group before at prefixNN
        omega
      · have later := rest.locked_group_energy Generated.soko1_2_potential_valid middleUnique
          (endGroup group before) oldGroup.1 oldGroup.2
          [184,210] CageLedger12.locked_184210 (by decide +kernel) (List.Subset.trans pair locks)
        change debtOf p [184,210] ≤ energy p (endGroup group before) (outcome::after) at later
        have amount : (4 : Int) ≤ debtOf p [184,210] := by decide +kernel
        rw [shape,TokenAccounting.energy_append]
        change 0 ≤ ownSlack p group before at prefixNN
        omega
  · obtain ⟨j,hero,locks⟩ := terminal
    have finalInside := logged.end_subset initialUnique group unique subset
    have count := List.Nodup.length_le_of_subset (Cage10.unique j) (List.Subset.trans locks finalInside.2)
    have size : ∀ j, 2 < (Cage10.locks j).length := by decide +kernel
    have big := size j
    have finalReached := reached.append logged.trace
    have conserved := finalReached.conservation
    have empty : final.holes=[] := completed
    change 20 + final.holes.length = final.boulders.length + 18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega
#print axioms energy_four
end Owner1007.CageFour12
