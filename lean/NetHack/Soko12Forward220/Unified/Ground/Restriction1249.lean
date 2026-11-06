import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1249_0_checked : (List.range' 639488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1249_1_checked : (List.range' 639616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1249_2_checked : (List.range' 639744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1249_3_checked : (List.range' 639872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1249_range (index : Nat) (lower : 639488 ≤ index) (upper : index < 640000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 639744 then
    if cut : index < 639616 then
      exact segment_sound _ 639488 128 Restriction1249_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 639616 128 Restriction1249_1_checked index (by omega) (by omega)
  else
    if cut : index < 639872 then
      exact segment_sound _ 639744 128 Restriction1249_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 639872 128 Restriction1249_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
