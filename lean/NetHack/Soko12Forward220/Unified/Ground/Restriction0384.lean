import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0384_0_checked : (List.range' 196608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0384_1_checked : (List.range' 196736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0384_2_checked : (List.range' 196864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0384_3_checked : (List.range' 196992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0384_range (index : Nat) (lower : 196608 ≤ index) (upper : index < 197120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 196864 then
    if cut : index < 196736 then
      exact segment_sound _ 196608 128 Restriction0384_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 196736 128 Restriction0384_1_checked index (by omega) (by omega)
  else
    if cut : index < 196992 then
      exact segment_sound _ 196864 128 Restriction0384_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 196992 128 Restriction0384_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
