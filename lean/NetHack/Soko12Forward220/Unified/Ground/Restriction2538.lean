import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2538_0_checked : (List.range' 1299456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2538_1_checked : (List.range' 1299584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2538_2_checked : (List.range' 1299712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2538_3_checked : (List.range' 1299840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2538_range (index : Nat) (lower : 1299456 ≤ index) (upper : index < 1299968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1299712 then
    if cut : index < 1299584 then
      exact segment_sound _ 1299456 128 Restriction2538_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1299584 128 Restriction2538_1_checked index (by omega) (by omega)
  else
    if cut : index < 1299840 then
      exact segment_sound _ 1299712 128 Restriction2538_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1299840 128 Restriction2538_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
