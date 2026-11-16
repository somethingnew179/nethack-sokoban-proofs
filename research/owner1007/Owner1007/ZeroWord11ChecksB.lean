import Owner1007.ZeroWord11Data
namespace Owner1007.ZeroWord11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem walk14 : walkNodeCheck 14 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 14) hero target dir inside adjacent floor different notHole
theorem push14 : pushNodeCheck 14 = true := by decide +kernel
theorem node14 : nodeCheck 14 = true := Bool.and_eq_true_iff.mpr ⟨walk14, push14⟩
theorem walk15 : walkNodeCheck 15 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 15) hero target dir inside adjacent floor different notHole
theorem push15 : pushNodeCheck 15 = true := by decide +kernel
theorem node15 : nodeCheck 15 = true := Bool.and_eq_true_iff.mpr ⟨walk15, push15⟩
theorem walk16 : walkNodeCheck 16 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 16) hero target dir inside adjacent floor different notHole
theorem push16 : pushNodeCheck 16 = true := by decide +kernel
theorem node16 : nodeCheck 16 = true := Bool.and_eq_true_iff.mpr ⟨walk16, push16⟩
theorem walk17 : walkNodeCheck 17 = true := by decide +kernel
theorem push17 : pushNodeCheck 17 = true := by decide +kernel
theorem node17 : nodeCheck 17 = true := Bool.and_eq_true_iff.mpr ⟨walk17, push17⟩
theorem walk18 : walkNodeCheck 18 = true := by decide +kernel
theorem push18 : pushNodeCheck 18 = true := by decide +kernel
theorem node18 : nodeCheck 18 = true := Bool.and_eq_true_iff.mpr ⟨walk18, push18⟩
theorem walk19 : walkNodeCheck 19 = true := by decide +kernel
theorem push19 : pushNodeCheck 19 = true := by decide +kernel
theorem node19 : nodeCheck 19 = true := Bool.and_eq_true_iff.mpr ⟨walk19, push19⟩
theorem walk20 : walkNodeCheck 20 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 20) hero target dir inside adjacent floor different notHole
theorem push20 : pushNodeCheck 20 = true := by decide +kernel
theorem node20 : nodeCheck 20 = true := Bool.and_eq_true_iff.mpr ⟨walk20, push20⟩
theorem walk21 : walkNodeCheck 21 = true := by decide +kernel
theorem push21 : pushNodeCheck 21 = true := by decide +kernel
theorem node21 : nodeCheck 21 = true := Bool.and_eq_true_iff.mpr ⟨walk21, push21⟩
theorem walk22 : walkNodeCheck 22 = true := by decide +kernel
theorem push22 : pushNodeCheck 22 = true := by decide +kernel
theorem node22 : nodeCheck 22 = true := Bool.and_eq_true_iff.mpr ⟨walk22, push22⟩
theorem walk23 : walkNodeCheck 23 = true := by decide +kernel
theorem push23 : pushNodeCheck 23 = true := by decide +kernel
theorem node23 : nodeCheck 23 = true := Bool.and_eq_true_iff.mpr ⟨walk23, push23⟩
theorem walk24 : walkNodeCheck 24 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 24) hero target dir inside adjacent floor different notHole
theorem push24 : pushNodeCheck 24 = true := by decide +kernel
theorem node24 : nodeCheck 24 = true := Bool.and_eq_true_iff.mpr ⟨walk24, push24⟩
theorem walk25 : walkNodeCheck 25 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 25) hero target dir inside adjacent floor different notHole
theorem push25 : pushNodeCheck 25 = true := by decide +kernel
theorem node25 : nodeCheck 25 = true := Bool.and_eq_true_iff.mpr ⟨walk25, push25⟩
theorem walk26 : walkNodeCheck 26 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 26) hero target dir inside adjacent floor different notHole
theorem push26 : pushNodeCheck 26 = true := by decide +kernel
theorem node26 : nodeCheck 26 = true := Bool.and_eq_true_iff.mpr ⟨walk26, push26⟩
theorem walk27 : walkNodeCheck 27 = true := by
  apply walk_of_closed
  intro hero inside dir target adjacent floor door different notHole clear
  exact full_remove_walk (cell 27) hero target dir inside adjacent floor different notHole
theorem push27 : pushNodeCheck 27 = true := by decide +kernel
theorem node27 : nodeCheck 27 = true := Bool.and_eq_true_iff.mpr ⟨walk27, push27⟩
#print axioms node27
end Owner1007.ZeroWord11
