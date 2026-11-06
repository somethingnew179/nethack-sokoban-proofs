import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2163_0_checked : (List.range' 1107456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2163_1_checked : (List.range' 1107584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2163_2_checked : (List.range' 1107712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2163_3_checked : (List.range' 1107840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2163_range (index : Nat) (lower : 1107456 ≤ index) (upper : index < 1107968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1107712 then
    if cut : index < 1107584 then
      exact segment_sound _ 1107456 128 Restriction2163_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1107584 128 Restriction2163_1_checked index (by omega) (by omega)
  else
    if cut : index < 1107840 then
      exact segment_sound _ 1107712 128 Restriction2163_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1107840 128 Restriction2163_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
