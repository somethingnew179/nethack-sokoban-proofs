import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1444_0_checked : (List.range' 739328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1444_1_checked : (List.range' 739456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1444_2_checked : (List.range' 739584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1444_3_checked : (List.range' 739712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1444_range (index : Nat) (lower : 739328 ≤ index) (upper : index < 739840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 739584 then
    if cut : index < 739456 then
      exact segment_sound _ 739328 128 Restriction1444_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 739456 128 Restriction1444_1_checked index (by omega) (by omega)
  else
    if cut : index < 739712 then
      exact segment_sound _ 739584 128 Restriction1444_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 739712 128 Restriction1444_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
