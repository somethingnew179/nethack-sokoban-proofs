import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0305_0_checked : (List.range' 156160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0305_1_checked : (List.range' 156288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0305_2_checked : (List.range' 156416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0305_3_checked : (List.range' 156544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0305_range (index : Nat) (lower : 156160 ≤ index) (upper : index < 156672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 156416 then
    if cut : index < 156288 then
      exact segment_sound _ 156160 128 Restriction0305_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 156288 128 Restriction0305_1_checked index (by omega) (by omega)
  else
    if cut : index < 156544 then
      exact segment_sound _ 156416 128 Restriction0305_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 156544 128 Restriction0305_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
