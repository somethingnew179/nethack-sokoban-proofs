import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1752_0_checked : (List.range' 897024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1752_1_checked : (List.range' 897152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1752_2_checked : (List.range' 897280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1752_3_checked : (List.range' 897408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1752_range (index : Nat) (lower : 897024 ≤ index) (upper : index < 897536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 897280 then
    if cut : index < 897152 then
      exact segment_sound _ 897024 128 Restriction1752_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 897152 128 Restriction1752_1_checked index (by omega) (by omega)
  else
    if cut : index < 897408 then
      exact segment_sound _ 897280 128 Restriction1752_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 897408 128 Restriction1752_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
