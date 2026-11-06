import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0824_0_checked : (List.range' 421888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0824_1_checked : (List.range' 422016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0824_2_checked : (List.range' 422144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0824_3_checked : (List.range' 422272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0824_range (index : Nat) (lower : 421888 ≤ index) (upper : index < 422400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 422144 then
    if cut : index < 422016 then
      exact segment_sound _ 421888 128 Restriction0824_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 422016 128 Restriction0824_1_checked index (by omega) (by omega)
  else
    if cut : index < 422272 then
      exact segment_sound _ 422144 128 Restriction0824_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 422272 128 Restriction0824_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
