import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0913_0_checked : (List.range' 467456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0913_1_checked : (List.range' 467584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0913_2_checked : (List.range' 467712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0913_3_checked : (List.range' 467840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0913_range (index : Nat) (lower : 467456 ≤ index) (upper : index < 467968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 467712 then
    if cut : index < 467584 then
      exact segment_sound _ 467456 128 Restriction0913_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 467584 128 Restriction0913_1_checked index (by omega) (by omega)
  else
    if cut : index < 467840 then
      exact segment_sound _ 467712 128 Restriction0913_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 467840 128 Restriction0913_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
