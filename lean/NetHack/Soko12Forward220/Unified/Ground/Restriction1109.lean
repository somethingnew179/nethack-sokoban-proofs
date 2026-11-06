import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1109_0_checked : (List.range' 567808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1109_1_checked : (List.range' 567936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1109_2_checked : (List.range' 568064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1109_3_checked : (List.range' 568192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1109_range (index : Nat) (lower : 567808 ≤ index) (upper : index < 568320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 568064 then
    if cut : index < 567936 then
      exact segment_sound _ 567808 128 Restriction1109_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 567936 128 Restriction1109_1_checked index (by omega) (by omega)
  else
    if cut : index < 568192 then
      exact segment_sound _ 568064 128 Restriction1109_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 568192 128 Restriction1109_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
