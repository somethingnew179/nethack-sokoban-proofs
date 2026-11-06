import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1179_0_checked : (List.range' 603648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1179_1_checked : (List.range' 603776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1179_2_checked : (List.range' 603904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1179_3_checked : (List.range' 604032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1179_range (index : Nat) (lower : 603648 ≤ index) (upper : index < 604160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 603904 then
    if cut : index < 603776 then
      exact segment_sound _ 603648 128 Restriction1179_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 603776 128 Restriction1179_1_checked index (by omega) (by omega)
  else
    if cut : index < 604032 then
      exact segment_sound _ 603904 128 Restriction1179_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 604032 128 Restriction1179_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
