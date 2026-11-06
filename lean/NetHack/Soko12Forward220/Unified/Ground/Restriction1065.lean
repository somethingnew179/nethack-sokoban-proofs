import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1065_0_checked : (List.range' 545280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1065_1_checked : (List.range' 545408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1065_2_checked : (List.range' 545536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1065_3_checked : (List.range' 545664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1065_range (index : Nat) (lower : 545280 ≤ index) (upper : index < 545792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 545536 then
    if cut : index < 545408 then
      exact segment_sound _ 545280 128 Restriction1065_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 545408 128 Restriction1065_1_checked index (by omega) (by omega)
  else
    if cut : index < 545664 then
      exact segment_sound _ 545536 128 Restriction1065_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 545664 128 Restriction1065_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
