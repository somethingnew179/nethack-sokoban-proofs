import Owner1007.Cage23912
import Owner1007.Post187Four12
namespace Owner1007.Cage239Six12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def postIndex (i : Fin 10) : Fin 10 := ⟨i.val%4,by omega⟩
theorem post_activation : ∀ j : Fin 10, 4≤j.val → j.val<8 →
 Post18712.locks (postIndex j) ⊆ 161::(Owner1007.Cage23912.locks j).erase 187 := by decide +kernel
theorem post_hero : ∀ j : Fin 10, 4≤j.val → j.val<8 → 187∈Post18712.region (postIndex j) := by decide +kernel
theorem escape_activation : ∀ j : Fin 10,
 Cage10.locks j ⊆ 265::(Owner1007.Cage23912.locks j).erase 239 := by decide +kernel
theorem escape_hero : ∀ j : Fin 10, 239∈Cage10.region j := by decide +kernel
theorem energy_six {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final) {i : Fin 10}
    (hero : state.player ∈ Owner1007.Cage23912.region i) (inside : Owner1007.Cage23912.locks i ⊆ group) :
    6 ≤ energy p group outcomes := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ Cage23912.matrix
  have initialUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed Owner1007.Cage23912.unique logged reached group unique subset hero inside with event | terminal
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
        have same : Owner1007.Cage23912.basic b = j := Fin.ext rfl
        have classified := Cage23912.classification b middle.player (by simpa only [same] using heroBefore)
          dir source (Owner1007.Cage23912.paid_sources source dir paid) adjacent paid
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
            (shift : small ⊆ dest :: (Owner1007.Cage23912.locks j).erase source) :
            debtOf p small ≤ energy p (update (endGroup group before) (.push source ending)) after := by
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            targets clear checked effect
          subst ending
          have kept := CageFour12.shifted_inside (Owner1007.Cage23912.unique j) locks owner shift
          exact last.locked_group_energy Generated.soko1_2_potential_valid nextActual
            (update (endGroup group before) (.push source (.stay dest))) nextUnique nextSubset
            small locked smallUnique kept

        rcases classified with blocked | upperEvent | gateEvent | squareEvent | quadEvent | escapeEvent | priceSix
        · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks oldGroup.2) checked effect blocked)
        · obtain ⟨rfl,rfl,lower,upper⟩ := upperEvent
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          have kept := CageFour12.shifted_inside (Owner1007.Cage23912.unique j) locks owner (post_activation j lower upper)
          have newHero : t.state.player∈Post18712.region (postIndex j) := by
            rw [matches_hero middle t (.push 187 (.stay 161)) effect]
            exact post_hero j lower upper
          have later := Post187Four12.energy_four last nextReached
            (update (endGroup group before) (.push 187 (.stay 161))) nextUnique nextSubset completed newHero kept
          change 4≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
          have one : (2:Int)≤slack p (.push 187 (.stay 161)) := by decide +kernel
          exact reserve 2 4 one later
        · obtain ⟨rfl,rfl,gateOrSquare⟩ := gateEvent
          rcases gateOrSquare with gate | square
          · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              (show pushTargets soko1_2.board 211 .north=[185] by decide +kernel)
              (by decide +kernel) checked effect
            subst ending
            have kept := CageFour12.shifted_inside (Owner1007.Cage23912.unique j) locks owner gate
            have newHero : t.state.player∈PriceTrap12Gate.region 0 := by
              rw [matches_hero middle t (.push 211 (.stay 185)) effect]
              decide +kernel
            have later := CageLedger12.gate_owned_nineteen last nextReached
              (update (endGroup group before) (.push 211 (.stay 185))) nextUnique nextSubset newHero kept
            change 19≤energy p (update (endGroup group before) (.push 211 (.stay 185))) after at later
            have bound := reserve 0 19 oneNN later
            omega
          · have later := lockedBound 185 (by decide +kernel) (by decide +kernel)
              [158,159,184,185] (by decide +kernel) CageLedger12.locked_upper_square square
            have amount : (6:Int)≤debtOf p [158,159,184,185] := by decide +kernel
            have bound := reserve 0 (debtOf p [158,159,184,185]) oneNN later
            omega
        · obtain ⟨which,shifted⟩ := squareEvent
          have targets : pushTargets soko1_2.board source dir=[Owner1007.Cage23912.squareDest source] := by
            rcases which with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel
          have clear : Owner1007.Cage23912.squareDest source∉soko1_2.initial.holes := by
            rcases which with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel
          have later := lockedBound (Owner1007.Cage23912.squareDest source) targets clear
            [186,187,212,213] (by decide +kernel) CageLedger12.locked_middle_square shifted
          have amount : (6:Int)≤debtOf p [186,187,212,213] := by decide +kernel
          have bound := reserve 0 (debtOf p [186,187,212,213]) oneNN later
          omega
        · obtain ⟨rfl,rfl,quad⟩ := quadEvent
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          have kept := CageFour12.shifted_inside (Owner1007.Cage23912.unique j) locks owner quad
          have newHero : t.state.player∈Quad211Trap12.region 0 := by
            rw [matches_hero middle t (.push 212 (.stay 211)) effect]
            decide +kernel
          have later := Quad211Trap12.owned_energy_fifteen last nextReached
            (update (endGroup group before) (.push 212 (.stay 211))) nextUnique nextSubset newHero kept
          change 15≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
          have bound := reserve 0 15 oneNN later
          omega
        · obtain ⟨rfl,rfl⟩ := escapeEvent
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            (show pushTargets soko1_2.board 239 .south=[265] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          have kept := CageFour12.shifted_inside (Owner1007.Cage23912.unique j) locks owner (escape_activation j)
          have newHero : t.state.player∈Cage10.region j := by
            rw [matches_hero middle t (.push 239 (.stay 265)) effect]
            exact escape_hero j
          have later := CageFour12.energy_four last nextReached
            (update (endGroup group before) (.push 239 (.stay 265))) nextUnique nextSubset completed newHero kept
          change 4≤energy p (update (endGroup group before) (.push 239 (.stay 265))) after at later
          have one : (2:Int)≤slack p (.push 239 (.stay 265)) := by decide +kernel
          exact reserve 2 4 one later
        · have one := push_effect_price p soko1_2.initial.holes 6 middleReached.holes_sublist.subset priceSix checked effect
          have bound := event_energy_le Generated.soko1_2_potential_valid group first last (.push source ending)
          simp only [projectedOutcome,if_pos owner] at bound
          rw [shape]
          change slack p (.push source ending)≤energy p group (before++(.push source ending)::after) at bound
          omega
    · have large : 8 ≤ j.val := by omega
      have pair := Owner1007.Cage23912.badPair j large
      have rest : Logged soko1_2.board middle (dir::afterDirs) final (t.pushCost+afterPushes) (1+afterMoves)
          (outcome::after) := .cons checked effect last
      rcases pair with pair | pair
      · have later := rest.locked_group_energy Generated.soko1_2_potential_valid middleUnique
          (endGroup group before) oldGroup.1 oldGroup.2
          [210,236] CageLedger12.locked_210236 (by decide +kernel) (List.Subset.trans pair locks)
        change debtOf p [210,236] ≤ energy p (endGroup group before) (outcome::after) at later
        have amount : (6 : Int) ≤ debtOf p [210,236] := by decide +kernel
        rw [shape,TokenAccounting.energy_append]
        change 0 ≤ ownSlack p group before at prefixNN
        omega
      · have later := rest.locked_group_energy Generated.soko1_2_potential_valid middleUnique
          (endGroup group before) oldGroup.1 oldGroup.2
          [184,210] CageLedger12.locked_184210 (by decide +kernel) (List.Subset.trans pair locks)
        change debtOf p [184,210] ≤ energy p (endGroup group before) (outcome::after) at later
        have amount : (6 : Int) ≤ debtOf p [184,210] := by decide +kernel
        rw [shape,TokenAccounting.energy_append]
        change 0 ≤ ownSlack p group before at prefixNN
        omega
  · obtain ⟨j,hero,locks⟩ := terminal
    have finalInside := logged.end_subset initialUnique group unique subset
    have count := List.Nodup.length_le_of_subset (Owner1007.Cage23912.unique j) (List.Subset.trans locks finalInside.2)
    have size : ∀ j, 2 < (Owner1007.Cage23912.locks j).length := by decide +kernel
    have big := size j
    have finalReached := reached.append logged.trace
    have conserved := finalReached.conservation
    have empty : final.holes=[] := completed
    change 20 + final.holes.length = final.boulders.length + 18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega
#print axioms energy_six
end Owner1007.Cage239Six12

