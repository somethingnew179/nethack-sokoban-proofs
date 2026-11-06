import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0740_0_checked : (List.range' 378880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0740_1_checked : (List.range' 379008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0740_2_checked : (List.range' 379136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0740_3_checked : (List.range' 379264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0740_range (index : Nat) (lower : 378880 ≤ index) (upper : index < 379392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 379136 then
    if cut : index < 379008 then
      exact segment_sound _ 378880 128 Restriction0740_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 379008 128 Restriction0740_1_checked index (by omega) (by omega)
  else
    if cut : index < 379264 then
      exact segment_sound _ 379136 128 Restriction0740_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 379264 128 Restriction0740_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
