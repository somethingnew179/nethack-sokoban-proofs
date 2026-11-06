import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0497_0_checked : (List.range' 254464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0497_1_checked : (List.range' 254592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0497_2_checked : (List.range' 254720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0497_3_checked : (List.range' 254848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0497_range (index : Nat) (lower : 254464 ≤ index) (upper : index < 254976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 254720 then
    if cut : index < 254592 then
      exact segment_sound _ 254464 128 Restriction0497_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 254592 128 Restriction0497_1_checked index (by omega) (by omega)
  else
    if cut : index < 254848 then
      exact segment_sound _ 254720 128 Restriction0497_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 254848 128 Restriction0497_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
