import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2077_0_checked : (List.range' 1063424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2077_1_checked : (List.range' 1063552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2077_2_checked : (List.range' 1063680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2077_3_checked : (List.range' 1063808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2077_range (index : Nat) (lower : 1063424 ≤ index) (upper : index < 1063936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1063680 then
    if cut : index < 1063552 then
      exact segment_sound _ 1063424 128 Restriction2077_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1063552 128 Restriction2077_1_checked index (by omega) (by omega)
  else
    if cut : index < 1063808 then
      exact segment_sound _ 1063680 128 Restriction2077_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1063808 128 Restriction2077_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
