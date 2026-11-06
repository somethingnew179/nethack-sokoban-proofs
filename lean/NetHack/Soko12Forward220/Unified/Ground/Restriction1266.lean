import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1266_0_checked : (List.range' 648192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1266_1_checked : (List.range' 648320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1266_2_checked : (List.range' 648448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1266_3_checked : (List.range' 648576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1266_range (index : Nat) (lower : 648192 ≤ index) (upper : index < 648704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 648448 then
    if cut : index < 648320 then
      exact segment_sound _ 648192 128 Restriction1266_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 648320 128 Restriction1266_1_checked index (by omega) (by omega)
  else
    if cut : index < 648576 then
      exact segment_sound _ 648448 128 Restriction1266_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 648576 128 Restriction1266_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
