import Owner1007.LeftInwardStart11
import Owner1007.ForwardPrices11
import Owner1007.ForwardSnapshots11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.ForwardInwardImpossible11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def source (i : Fin 2) : Cell := if i.val=0 then 137 else 139
def direction (i : Fin 2) : Dir := if i.val=0 then .east else .west
theorem different : ∀i,source i≠LeftInwardStart11.other i := by decide +kernel
theorem shift : ∀i,(update [137,139,185,187,189] (.push (source i) (.stay 138))).Perm (LeftInwardStart11.locks i) := by decide +kernel
theorem next_hero : ∀i,source i∈LeftInwardStart11.region i := by decide +kernel
theorem impossible {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (i : Fin 2) (head : step soko1_1.board state (direction i)=some t)
 (effect : Matches state t (.push (source i) (.stay 138)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (capUpper : energy soko1_1.initial final UpperBudget11.U6 (before++.push (source i) (.stay 138)::after)≤6)
 (capLeft : energy soko1_1.initial final [186] (before++.push (source i) (.stay 138)::after)≤2)
 (capRest : energy soko1_1.initial final UpperBudget11.Rest (before++.push (source i) (.stay 138)::after)<2)
 (prefixUpper : 4≤energy soko1_1.initial state UpperBudget11.U6 before)
 (prefixLeft : 2≤energy soko1_1.initial state [186] before)
 (same : (endGroup ForwardSnapshots11.G before).Perm [137,139,185,187,189])
 (stationary : ownPushes [LeftInwardStart11.other i] before=0) : False := by
 let headLogged : Logged soko1_1.board state [direction i] t.state t.pushCost 1 [.push (source i) (.stay 138)] :=
  .cons head effect (.nil _)
 let lead := first.append headLogged
 let whole := first.append (Logged.cons head effect last)
 let chosen := endGroup ForwardSnapshots11.G (before++[.push (source i) (.stay 138)])
 have nextSame : chosen.Perm (LeftInwardStart11.locks i) := by
  dsimp only [chosen]
  rw [endGroup_append]
  exact (update_perm same _).trans (shift i)
 have facts := lead.end_subset (by decide) ForwardSnapshots11.G (by decide) (by decide)
 have hero : t.state.player∈LeftInwardStart11.region i := by rw [effect.2];exact next_hero i
 have tagOther := no_push_unchanged [LeftInwardStart11.other i] before stationary
 have noSource : source i∉[LeftInwardStart11.other i] := by simpa using different i
 have nextStationary : ownPushes [LeftInwardStart11.other i] (before++[.push (source i) (.stay 138)])=0 := by
  rw [ownPushes_append,tagOther]
  simp only [ownPushes,ownPush,if_neg noSource,Nat.zero_add,Nat.add_zero,stationary]
 have globalGone := ForwardSnapshots11.gone whole completed capUpper capLeft
 have gone : endGroup chosen after=[] := by
  dsimp only [chosen]
  rw [←endGroup_append]
  simpa only [List.append_assoc,List.singleton_append] using globalGone
 have upperEight : energy soko1_1.initial final UpperBudget11.U6 ((before++[.push (source i) (.stay 138)])++after)≤8 := by
  simpa only [List.append_assoc,List.singleton_append] using (show energy soko1_1.initial final UpperBudget11.U6 (before++.push (source i) (.stay 138)::after)≤8 by omega)
 have restCheap : energy soko1_1.initial final UpperBudget11.Rest ((before++[.push (source i) (.stay 138)])++after)<2 := by
  simpa only [List.append_assoc,List.singleton_append] using capRest
 have reserve := LeftInwardStart11.future_four lead last completed upperEight restCheap i nextStationary
  chosen facts.1 facts.2 nextSame hero gone
 have monoUpper := prefix_energy_le first headLogged UpperBudget11.U6 (by decide) (by decide)
 have monoLeft := prefix_energy_le first headLogged [186] (by decide) (by decide)
 have nextUpper : 4≤energy soko1_1.initial t.state UpperBudget11.U6 (before++[.push (source i) (.stay 138)]) := by omega
 have nextLeft : 2≤energy soko1_1.initial t.state [186] (before++[.push (source i) (.stay 138)]) := by omega
 have selected := end_subset_selected lead (by decide) ForwardSnapshots11.G ForwardPrices11.S (by decide) (by decide) (by decide) (by decide)
 have upperSix : energy soko1_1.initial final UpperBudget11.U6 ((before++[.push (source i) (.stay 138)])++after)≤6 := by
  simpa only [List.append_assoc,List.singleton_append] using capUpper
 have leftTwo : energy soko1_1.initial final [186] ((before++[.push (source i) (.stay 138)])++after)≤2 := by
  simpa only [List.append_assoc,List.singleton_append] using capLeft
 have budget := ForwardPrices11.tail_cap lead last upperSix leftTwo nextUpper nextLeft chosen facts.1 selected
 omega
#print axioms impossible
end Owner1007.ForwardInwardImpossible11
