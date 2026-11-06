import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0315_0_checked : (List.range' 161280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0315_1_checked : (List.range' 161408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0315_2_checked : (List.range' 161536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0315_3_checked : (List.range' 161664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0315_range (index : Nat) (lower : 161280 ≤ index) (upper : index < 161792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 161536 then
    if cut : index < 161408 then
      exact segment_sound _ 161280 128 Restriction0315_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 161408 128 Restriction0315_1_checked index (by omega) (by omega)
  else
    if cut : index < 161664 then
      exact segment_sound _ 161536 128 Restriction0315_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 161664 128 Restriction0315_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
