import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1078_0_checked : (List.range' 551936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1078_1_checked : (List.range' 552064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1078_2_checked : (List.range' 552192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1078_3_checked : (List.range' 552320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1078_range (index : Nat) (lower : 551936 ≤ index) (upper : index < 552448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 552192 then
    if cut : index < 552064 then
      exact segment_sound _ 551936 128 Restriction1078_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 552064 128 Restriction1078_1_checked index (by omega) (by omega)
  else
    if cut : index < 552320 then
      exact segment_sound _ 552192 128 Restriction1078_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 552320 128 Restriction1078_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
