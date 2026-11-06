import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1515_0_checked : (List.range' 775680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1515_1_checked : (List.range' 775808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1515_2_checked : (List.range' 775936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1515_3_checked : (List.range' 776064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1515_range (index : Nat) (lower : 775680 ≤ index) (upper : index < 776192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 775936 then
    if cut : index < 775808 then
      exact segment_sound _ 775680 128 Restriction1515_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 775808 128 Restriction1515_1_checked index (by omega) (by omega)
  else
    if cut : index < 776064 then
      exact segment_sound _ 775936 128 Restriction1515_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 776064 128 Restriction1515_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
