import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0555_0_checked : (List.range' 284160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0555_1_checked : (List.range' 284288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0555_2_checked : (List.range' 284416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0555_3_checked : (List.range' 284544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0555_range (index : Nat) (lower : 284160 ≤ index) (upper : index < 284672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 284416 then
    if cut : index < 284288 then
      exact segment_sound _ 284160 128 Restriction0555_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 284288 128 Restriction0555_1_checked index (by omega) (by omega)
  else
    if cut : index < 284544 then
      exact segment_sound _ 284416 128 Restriction0555_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 284544 128 Restriction0555_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
