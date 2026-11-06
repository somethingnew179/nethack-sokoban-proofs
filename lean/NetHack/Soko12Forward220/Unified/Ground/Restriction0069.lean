import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0069_0_checked : (List.range' 35328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0069_1_checked : (List.range' 35456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0069_2_checked : (List.range' 35584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0069_3_checked : (List.range' 35712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0069_range (index : Nat) (lower : 35328 ≤ index) (upper : index < 35840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 35584 then
    if cut : index < 35456 then
      exact segment_sound _ 35328 128 Restriction0069_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 35456 128 Restriction0069_1_checked index (by omega) (by omega)
  else
    if cut : index < 35712 then
      exact segment_sound _ 35584 128 Restriction0069_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 35712 128 Restriction0069_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
