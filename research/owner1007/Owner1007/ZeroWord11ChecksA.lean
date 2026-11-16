import Owner1007.ZeroWord11Data
namespace Owner1007.ZeroWord11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem walk0 : walkNodeCheck 0 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 0) hero target dir inside adjacent floor different notHole
theorem push0 : pushNodeCheck 0 = true := by decide +kernel
theorem node0 : nodeCheck 0 = true := Bool.and_eq_true_iff.mpr ⟨walk0, push0⟩
theorem walk1 : walkNodeCheck 1 = true := by decide +kernel
theorem push1 : pushNodeCheck 1 = true := by decide +kernel
theorem node1 : nodeCheck 1 = true := Bool.and_eq_true_iff.mpr ⟨walk1, push1⟩
theorem walk2 : walkNodeCheck 2 = true := by decide +kernel
theorem push2 : pushNodeCheck 2 = true := by decide +kernel
theorem node2 : nodeCheck 2 = true := Bool.and_eq_true_iff.mpr ⟨walk2, push2⟩
theorem walk3 : walkNodeCheck 3 = true := by decide +kernel
theorem push3 : pushNodeCheck 3 = true := by decide +kernel
theorem node3 : nodeCheck 3 = true := Bool.and_eq_true_iff.mpr ⟨walk3, push3⟩
theorem walk4 : walkNodeCheck 4 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 4) hero target dir inside adjacent floor different notHole
theorem push4 : pushNodeCheck 4 = true := by decide +kernel
theorem node4 : nodeCheck 4 = true := Bool.and_eq_true_iff.mpr ⟨walk4, push4⟩
theorem walk5 : walkNodeCheck 5 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 5) hero target dir inside adjacent floor different notHole
theorem push5 : pushNodeCheck 5 = true := by decide +kernel
theorem node5 : nodeCheck 5 = true := Bool.and_eq_true_iff.mpr ⟨walk5, push5⟩
theorem walk6 : walkNodeCheck 6 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 6) hero target dir inside adjacent floor different notHole
theorem push6 : pushNodeCheck 6 = true := by decide +kernel
theorem node6 : nodeCheck 6 = true := Bool.and_eq_true_iff.mpr ⟨walk6, push6⟩
theorem walk7 : walkNodeCheck 7 = true := by decide +kernel
theorem push7 : pushNodeCheck 7 = true := by decide +kernel
theorem node7 : nodeCheck 7 = true := Bool.and_eq_true_iff.mpr ⟨walk7, push7⟩
theorem walk8 : walkNodeCheck 8 = true := by decide +kernel
theorem push8 : pushNodeCheck 8 = true := by decide +kernel
theorem node8 : nodeCheck 8 = true := Bool.and_eq_true_iff.mpr ⟨walk8, push8⟩
theorem walk9 : walkNodeCheck 9 = true := by decide +kernel
theorem push9 : pushNodeCheck 9 = true := by decide +kernel
theorem node9 : nodeCheck 9 = true := Bool.and_eq_true_iff.mpr ⟨walk9, push9⟩
theorem walk10 : walkNodeCheck 10 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 10) hero target dir inside adjacent floor different notHole
theorem push10 : pushNodeCheck 10 = true := by decide +kernel
theorem node10 : nodeCheck 10 = true := Bool.and_eq_true_iff.mpr ⟨walk10, push10⟩
theorem walk11 : walkNodeCheck 11 = true := by decide +kernel
theorem push11 : pushNodeCheck 11 = true := by decide +kernel
theorem node11 : nodeCheck 11 = true := Bool.and_eq_true_iff.mpr ⟨walk11, push11⟩
theorem walk12 : walkNodeCheck 12 = true := by decide +kernel
theorem push12 : pushNodeCheck 12 = true := by decide +kernel
theorem node12 : nodeCheck 12 = true := Bool.and_eq_true_iff.mpr ⟨walk12, push12⟩
theorem walk13 : walkNodeCheck 13 = true := by decide +kernel
theorem push13 : pushNodeCheck 13 = true := by decide +kernel
theorem node13 : nodeCheck 13 = true := Bool.and_eq_true_iff.mpr ⟨walk13, push13⟩
#print axioms node13
end Owner1007.ZeroWord11
