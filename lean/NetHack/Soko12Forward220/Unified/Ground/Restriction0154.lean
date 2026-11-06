import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0154_0_checked : (List.range' 78848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0154_1_checked : (List.range' 78976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0154_2_checked : (List.range' 79104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0154_3_checked : (List.range' 79232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0154_range (index : Nat) (lower : 78848 ≤ index) (upper : index < 79360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 79104 then
    if cut : index < 78976 then
      exact segment_sound _ 78848 128 Restriction0154_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 78976 128 Restriction0154_1_checked index (by omega) (by omega)
  else
    if cut : index < 79232 then
      exact segment_sound _ 79104 128 Restriction0154_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 79232 128 Restriction0154_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
