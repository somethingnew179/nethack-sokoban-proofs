import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0430_0_checked : (List.range' 220160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0430_1_checked : (List.range' 220288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0430_2_checked : (List.range' 220416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0430_3_checked : (List.range' 220544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0430_range (index : Nat) (lower : 220160 ≤ index) (upper : index < 220672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 220416 then
    if cut : index < 220288 then
      exact segment_sound _ 220160 128 Restriction0430_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 220288 128 Restriction0430_1_checked index (by omega) (by omega)
  else
    if cut : index < 220544 then
      exact segment_sound _ 220416 128 Restriction0430_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 220544 128 Restriction0430_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
