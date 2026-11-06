import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0292_0_checked : (List.range' 149504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0292_1_checked : (List.range' 149632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0292_2_checked : (List.range' 149760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0292_3_checked : (List.range' 149888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0292_range (index : Nat) (lower : 149504 ≤ index) (upper : index < 150016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 149760 then
    if cut : index < 149632 then
      exact segment_sound _ 149504 128 Restriction0292_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 149632 128 Restriction0292_1_checked index (by omega) (by omega)
  else
    if cut : index < 149888 then
      exact segment_sound _ 149760 128 Restriction0292_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 149888 128 Restriction0292_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
