import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1180_0_checked : (List.range' 604160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1180_1_checked : (List.range' 604288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1180_2_checked : (List.range' 604416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1180_3_checked : (List.range' 604544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1180_range (index : Nat) (lower : 604160 ≤ index) (upper : index < 604672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 604416 then
    if cut : index < 604288 then
      exact segment_sound _ 604160 128 Restriction1180_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 604288 128 Restriction1180_1_checked index (by omega) (by omega)
  else
    if cut : index < 604544 then
      exact segment_sound _ 604416 128 Restriction1180_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 604544 128 Restriction1180_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
