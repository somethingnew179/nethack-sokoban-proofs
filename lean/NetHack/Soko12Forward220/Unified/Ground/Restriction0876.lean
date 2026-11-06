import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0876_0_checked : (List.range' 448512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0876_1_checked : (List.range' 448640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0876_2_checked : (List.range' 448768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0876_3_checked : (List.range' 448896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0876_range (index : Nat) (lower : 448512 ≤ index) (upper : index < 449024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 448768 then
    if cut : index < 448640 then
      exact segment_sound _ 448512 128 Restriction0876_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 448640 128 Restriction0876_1_checked index (by omega) (by omega)
  else
    if cut : index < 448896 then
      exact segment_sound _ 448768 128 Restriction0876_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 448896 128 Restriction0876_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
