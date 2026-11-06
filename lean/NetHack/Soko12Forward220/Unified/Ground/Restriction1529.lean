import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1529_0_checked : (List.range' 782848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1529_1_checked : (List.range' 782976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1529_2_checked : (List.range' 783104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1529_3_checked : (List.range' 783232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1529_range (index : Nat) (lower : 782848 ≤ index) (upper : index < 783360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 783104 then
    if cut : index < 782976 then
      exact segment_sound _ 782848 128 Restriction1529_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 782976 128 Restriction1529_1_checked index (by omega) (by omega)
  else
    if cut : index < 783232 then
      exact segment_sound _ 783104 128 Restriction1529_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 783232 128 Restriction1529_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
