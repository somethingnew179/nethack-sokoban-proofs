import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2090_0_checked : (List.range' 1070080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2090_1_checked : (List.range' 1070208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2090_2_checked : (List.range' 1070336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2090_3_checked : (List.range' 1070464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2090_range (index : Nat) (lower : 1070080 ≤ index) (upper : index < 1070592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1070336 then
    if cut : index < 1070208 then
      exact segment_sound _ 1070080 128 Restriction2090_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1070208 128 Restriction2090_1_checked index (by omega) (by omega)
  else
    if cut : index < 1070464 then
      exact segment_sound _ 1070336 128 Restriction2090_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1070464 128 Restriction2090_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
