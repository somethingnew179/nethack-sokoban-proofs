import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0790_0_checked : (List.range' 404480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0790_1_checked : (List.range' 404608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0790_2_checked : (List.range' 404736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0790_3_checked : (List.range' 404864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0790_range (index : Nat) (lower : 404480 ≤ index) (upper : index < 404992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 404736 then
    if cut : index < 404608 then
      exact segment_sound _ 404480 128 Restriction0790_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 404608 128 Restriction0790_1_checked index (by omega) (by omega)
  else
    if cut : index < 404864 then
      exact segment_sound _ 404736 128 Restriction0790_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 404864 128 Restriction0790_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
