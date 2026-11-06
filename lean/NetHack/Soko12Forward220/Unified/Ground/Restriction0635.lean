import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0635_0_checked : (List.range' 325120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0635_1_checked : (List.range' 325248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0635_2_checked : (List.range' 325376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0635_3_checked : (List.range' 325504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0635_range (index : Nat) (lower : 325120 ≤ index) (upper : index < 325632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 325376 then
    if cut : index < 325248 then
      exact segment_sound _ 325120 128 Restriction0635_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 325248 128 Restriction0635_1_checked index (by omega) (by omega)
  else
    if cut : index < 325504 then
      exact segment_sound _ 325376 128 Restriction0635_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 325504 128 Restriction0635_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
