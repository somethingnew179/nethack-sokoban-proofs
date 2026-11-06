import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1535_0_checked : (List.range' 785920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1535_1_checked : (List.range' 786048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1535_2_checked : (List.range' 786176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1535_3_checked : (List.range' 786304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1535_range (index : Nat) (lower : 785920 ≤ index) (upper : index < 786432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 786176 then
    if cut : index < 786048 then
      exact segment_sound _ 785920 128 Restriction1535_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 786048 128 Restriction1535_1_checked index (by omega) (by omega)
  else
    if cut : index < 786304 then
      exact segment_sound _ 786176 128 Restriction1535_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 786304 128 Restriction1535_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
