import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1062_0_checked : (List.range' 543744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1062_1_checked : (List.range' 543872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1062_2_checked : (List.range' 544000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1062_3_checked : (List.range' 544128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1062_range (index : Nat) (lower : 543744 ≤ index) (upper : index < 544256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 544000 then
    if cut : index < 543872 then
      exact segment_sound _ 543744 128 Restriction1062_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 543872 128 Restriction1062_1_checked index (by omega) (by omega)
  else
    if cut : index < 544128 then
      exact segment_sound _ 544000 128 Restriction1062_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 544128 128 Restriction1062_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
