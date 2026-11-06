import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0456_0_checked : (List.range' 233472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0456_1_checked : (List.range' 233600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0456_2_checked : (List.range' 233728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0456_3_checked : (List.range' 233856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0456_range (index : Nat) (lower : 233472 ≤ index) (upper : index < 233984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 233728 then
    if cut : index < 233600 then
      exact segment_sound _ 233472 128 Restriction0456_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 233600 128 Restriction0456_1_checked index (by omega) (by omega)
  else
    if cut : index < 233856 then
      exact segment_sound _ 233728 128 Restriction0456_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 233856 128 Restriction0456_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
