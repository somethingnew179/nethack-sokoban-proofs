import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2225_0_checked : (List.range' 1139200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2225_1_checked : (List.range' 1139328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2225_2_checked : (List.range' 1139456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2225_3_checked : (List.range' 1139584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2225_range (index : Nat) (lower : 1139200 ≤ index) (upper : index < 1139712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1139456 then
    if cut : index < 1139328 then
      exact segment_sound _ 1139200 128 Restriction2225_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1139328 128 Restriction2225_1_checked index (by omega) (by omega)
  else
    if cut : index < 1139584 then
      exact segment_sound _ 1139456 128 Restriction2225_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1139584 128 Restriction2225_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
