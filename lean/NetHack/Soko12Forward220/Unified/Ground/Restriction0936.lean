import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0936_0_checked : (List.range' 479232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0936_1_checked : (List.range' 479360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0936_2_checked : (List.range' 479488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0936_3_checked : (List.range' 479616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0936_range (index : Nat) (lower : 479232 ≤ index) (upper : index < 479744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 479488 then
    if cut : index < 479360 then
      exact segment_sound _ 479232 128 Restriction0936_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 479360 128 Restriction0936_1_checked index (by omega) (by omega)
  else
    if cut : index < 479616 then
      exact segment_sound _ 479488 128 Restriction0936_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 479616 128 Restriction0936_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
