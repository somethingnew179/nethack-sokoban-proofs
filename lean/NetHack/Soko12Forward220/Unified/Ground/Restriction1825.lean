import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1825_0_checked : (List.range' 934400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1825_1_checked : (List.range' 934528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1825_2_checked : (List.range' 934656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1825_3_checked : (List.range' 934784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1825_range (index : Nat) (lower : 934400 ≤ index) (upper : index < 934912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 934656 then
    if cut : index < 934528 then
      exact segment_sound _ 934400 128 Restriction1825_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 934528 128 Restriction1825_1_checked index (by omega) (by omega)
  else
    if cut : index < 934784 then
      exact segment_sound _ 934656 128 Restriction1825_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 934784 128 Restriction1825_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
