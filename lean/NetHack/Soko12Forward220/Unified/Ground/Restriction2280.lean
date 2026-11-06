import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2280_0_checked : (List.range' 1167360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2280_1_checked : (List.range' 1167488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2280_2_checked : (List.range' 1167616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2280_3_checked : (List.range' 1167744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2280_range (index : Nat) (lower : 1167360 ≤ index) (upper : index < 1167872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1167616 then
    if cut : index < 1167488 then
      exact segment_sound _ 1167360 128 Restriction2280_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1167488 128 Restriction2280_1_checked index (by omega) (by omega)
  else
    if cut : index < 1167744 then
      exact segment_sound _ 1167616 128 Restriction2280_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1167744 128 Restriction2280_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
