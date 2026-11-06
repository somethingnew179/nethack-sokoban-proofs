import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0645_0_checked : (List.range' 330240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0645_1_checked : (List.range' 330368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0645_2_checked : (List.range' 330496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0645_3_checked : (List.range' 330624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0645_range (index : Nat) (lower : 330240 ≤ index) (upper : index < 330752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 330496 then
    if cut : index < 330368 then
      exact segment_sound _ 330240 128 Restriction0645_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 330368 128 Restriction0645_1_checked index (by omega) (by omega)
  else
    if cut : index < 330624 then
      exact segment_sound _ 330496 128 Restriction0645_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 330624 128 Restriction0645_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
