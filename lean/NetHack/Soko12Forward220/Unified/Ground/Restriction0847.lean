import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0847_0_checked : (List.range' 433664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0847_1_checked : (List.range' 433792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0847_2_checked : (List.range' 433920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0847_3_checked : (List.range' 434048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0847_range (index : Nat) (lower : 433664 ≤ index) (upper : index < 434176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 433920 then
    if cut : index < 433792 then
      exact segment_sound _ 433664 128 Restriction0847_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 433792 128 Restriction0847_1_checked index (by omega) (by omega)
  else
    if cut : index < 434048 then
      exact segment_sound _ 433920 128 Restriction0847_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 434048 128 Restriction0847_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
