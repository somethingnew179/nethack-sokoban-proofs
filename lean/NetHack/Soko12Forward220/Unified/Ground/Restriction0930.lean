import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0930_0_checked : (List.range' 476160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0930_1_checked : (List.range' 476288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0930_2_checked : (List.range' 476416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0930_3_checked : (List.range' 476544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0930_range (index : Nat) (lower : 476160 ≤ index) (upper : index < 476672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 476416 then
    if cut : index < 476288 then
      exact segment_sound _ 476160 128 Restriction0930_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 476288 128 Restriction0930_1_checked index (by omega) (by omega)
  else
    if cut : index < 476544 then
      exact segment_sound _ 476416 128 Restriction0930_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 476544 128 Restriction0930_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
