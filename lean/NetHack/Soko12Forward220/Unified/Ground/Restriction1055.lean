import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1055_0_checked : (List.range' 540160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1055_1_checked : (List.range' 540288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1055_2_checked : (List.range' 540416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1055_3_checked : (List.range' 540544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1055_range (index : Nat) (lower : 540160 ≤ index) (upper : index < 540672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 540416 then
    if cut : index < 540288 then
      exact segment_sound _ 540160 128 Restriction1055_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 540288 128 Restriction1055_1_checked index (by omega) (by omega)
  else
    if cut : index < 540544 then
      exact segment_sound _ 540416 128 Restriction1055_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 540544 128 Restriction1055_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
