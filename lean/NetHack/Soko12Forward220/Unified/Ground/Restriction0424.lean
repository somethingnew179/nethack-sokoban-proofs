import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0424_0_checked : (List.range' 217088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0424_1_checked : (List.range' 217216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0424_2_checked : (List.range' 217344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0424_3_checked : (List.range' 217472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0424_range (index : Nat) (lower : 217088 ≤ index) (upper : index < 217600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 217344 then
    if cut : index < 217216 then
      exact segment_sound _ 217088 128 Restriction0424_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 217216 128 Restriction0424_1_checked index (by omega) (by omega)
  else
    if cut : index < 217472 then
      exact segment_sound _ 217344 128 Restriction0424_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 217472 128 Restriction0424_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
