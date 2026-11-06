import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2506_0_checked : (List.range' 1283072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2506_1_checked : (List.range' 1283200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2506_2_checked : (List.range' 1283328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2506_3_checked : (List.range' 1283456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2506_range (index : Nat) (lower : 1283072 ≤ index) (upper : index < 1283584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1283328 then
    if cut : index < 1283200 then
      exact segment_sound _ 1283072 128 Restriction2506_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1283200 128 Restriction2506_1_checked index (by omega) (by omega)
  else
    if cut : index < 1283456 then
      exact segment_sound _ 1283328 128 Restriction2506_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1283456 128 Restriction2506_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
