import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2288_0_checked : (List.range' 1171456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2288_1_checked : (List.range' 1171584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2288_2_checked : (List.range' 1171712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2288_3_checked : (List.range' 1171840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2288_range (index : Nat) (lower : 1171456 ≤ index) (upper : index < 1171968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1171712 then
    if cut : index < 1171584 then
      exact segment_sound _ 1171456 128 Restriction2288_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1171584 128 Restriction2288_1_checked index (by omega) (by omega)
  else
    if cut : index < 1171840 then
      exact segment_sound _ 1171712 128 Restriction2288_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1171840 128 Restriction2288_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
