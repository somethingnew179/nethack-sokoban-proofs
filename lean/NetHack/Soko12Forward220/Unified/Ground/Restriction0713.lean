import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0713_0_checked : (List.range' 365056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0713_1_checked : (List.range' 365184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0713_2_checked : (List.range' 365312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0713_3_checked : (List.range' 365440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0713_range (index : Nat) (lower : 365056 ≤ index) (upper : index < 365568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 365312 then
    if cut : index < 365184 then
      exact segment_sound _ 365056 128 Restriction0713_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 365184 128 Restriction0713_1_checked index (by omega) (by omega)
  else
    if cut : index < 365440 then
      exact segment_sound _ 365312 128 Restriction0713_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 365440 128 Restriction0713_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
