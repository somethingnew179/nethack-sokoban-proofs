import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2588_0_checked : (List.range' 1325056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2588_1_checked : (List.range' 1325184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2588_2_checked : (List.range' 1325312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2588_3_checked : (List.range' 1325440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2588_range (index : Nat) (lower : 1325056 ≤ index) (upper : index < 1325568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1325312 then
    if cut : index < 1325184 then
      exact segment_sound _ 1325056 128 Restriction2588_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1325184 128 Restriction2588_1_checked index (by omega) (by omega)
  else
    if cut : index < 1325440 then
      exact segment_sound _ 1325312 128 Restriction2588_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1325440 128 Restriction2588_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
