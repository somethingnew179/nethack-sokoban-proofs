import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2243_0_checked : (List.range' 1148416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2243_1_checked : (List.range' 1148544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2243_2_checked : (List.range' 1148672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2243_3_checked : (List.range' 1148800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2243_range (index : Nat) (lower : 1148416 ≤ index) (upper : index < 1148928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1148672 then
    if cut : index < 1148544 then
      exact segment_sound _ 1148416 128 Restriction2243_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1148544 128 Restriction2243_1_checked index (by omega) (by omega)
  else
    if cut : index < 1148800 then
      exact segment_sound _ 1148672 128 Restriction2243_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1148800 128 Restriction2243_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
