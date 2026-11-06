import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1573_0_checked : (List.range' 805376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1573_1_checked : (List.range' 805504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1573_2_checked : (List.range' 805632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1573_3_checked : (List.range' 805760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1573_range (index : Nat) (lower : 805376 ≤ index) (upper : index < 805888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 805632 then
    if cut : index < 805504 then
      exact segment_sound _ 805376 128 Restriction1573_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 805504 128 Restriction1573_1_checked index (by omega) (by omega)
  else
    if cut : index < 805760 then
      exact segment_sound _ 805632 128 Restriction1573_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 805760 128 Restriction1573_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
