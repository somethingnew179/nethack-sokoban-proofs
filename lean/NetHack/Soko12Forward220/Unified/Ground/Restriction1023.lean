import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1023_0_checked : (List.range' 523776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1023_1_checked : (List.range' 523904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1023_2_checked : (List.range' 524032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1023_3_checked : (List.range' 524160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1023_range (index : Nat) (lower : 523776 ≤ index) (upper : index < 524288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 524032 then
    if cut : index < 523904 then
      exact segment_sound _ 523776 128 Restriction1023_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 523904 128 Restriction1023_1_checked index (by omega) (by omega)
  else
    if cut : index < 524160 then
      exact segment_sound _ 524032 128 Restriction1023_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 524160 128 Restriction1023_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
