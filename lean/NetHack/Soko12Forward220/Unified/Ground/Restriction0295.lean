import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0295_0_checked : (List.range' 151040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0295_1_checked : (List.range' 151168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0295_2_checked : (List.range' 151296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0295_3_checked : (List.range' 151424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0295_range (index : Nat) (lower : 151040 ≤ index) (upper : index < 151552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 151296 then
    if cut : index < 151168 then
      exact segment_sound _ 151040 128 Restriction0295_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 151168 128 Restriction0295_1_checked index (by omega) (by omega)
  else
    if cut : index < 151424 then
      exact segment_sound _ 151296 128 Restriction0295_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 151424 128 Restriction0295_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
