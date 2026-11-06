import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0680_0_checked : (List.range' 348160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0680_1_checked : (List.range' 348288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0680_2_checked : (List.range' 348416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0680_3_checked : (List.range' 348544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0680_range (index : Nat) (lower : 348160 ≤ index) (upper : index < 348672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 348416 then
    if cut : index < 348288 then
      exact segment_sound _ 348160 128 Restriction0680_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 348288 128 Restriction0680_1_checked index (by omega) (by omega)
  else
    if cut : index < 348544 then
      exact segment_sound _ 348416 128 Restriction0680_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 348544 128 Restriction0680_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
