import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1531_0_checked : (List.range' 783872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1531_1_checked : (List.range' 784000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1531_2_checked : (List.range' 784128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1531_3_checked : (List.range' 784256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1531_range (index : Nat) (lower : 783872 ≤ index) (upper : index < 784384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 784128 then
    if cut : index < 784000 then
      exact segment_sound _ 783872 128 Restriction1531_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 784000 128 Restriction1531_1_checked index (by omega) (by omega)
  else
    if cut : index < 784256 then
      exact segment_sound _ 784128 128 Restriction1531_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 784256 128 Restriction1531_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
