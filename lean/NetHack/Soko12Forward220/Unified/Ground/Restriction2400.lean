import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2400_0_checked : (List.range' 1228800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2400_1_checked : (List.range' 1228928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2400_2_checked : (List.range' 1229056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2400_3_checked : (List.range' 1229184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2400_range (index : Nat) (lower : 1228800 ≤ index) (upper : index < 1229312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1229056 then
    if cut : index < 1228928 then
      exact segment_sound _ 1228800 128 Restriction2400_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1228928 128 Restriction2400_1_checked index (by omega) (by omega)
  else
    if cut : index < 1229184 then
      exact segment_sound _ 1229056 128 Restriction2400_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1229184 128 Restriction2400_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
