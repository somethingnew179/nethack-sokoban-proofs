import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0973_0_checked : (List.range' 498176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0973_1_checked : (List.range' 498304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0973_2_checked : (List.range' 498432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0973_3_checked : (List.range' 498560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0973_range (index : Nat) (lower : 498176 ≤ index) (upper : index < 498688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 498432 then
    if cut : index < 498304 then
      exact segment_sound _ 498176 128 Restriction0973_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 498304 128 Restriction0973_1_checked index (by omega) (by omega)
  else
    if cut : index < 498560 then
      exact segment_sound _ 498432 128 Restriction0973_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 498560 128 Restriction0973_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
