import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2419_0_checked : (List.range' 1238528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2419_1_checked : (List.range' 1238656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2419_2_checked : (List.range' 1238784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2419_3_checked : (List.range' 1238912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2419_range (index : Nat) (lower : 1238528 ≤ index) (upper : index < 1239040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1238784 then
    if cut : index < 1238656 then
      exact segment_sound _ 1238528 128 Restriction2419_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1238656 128 Restriction2419_1_checked index (by omega) (by omega)
  else
    if cut : index < 1238912 then
      exact segment_sound _ 1238784 128 Restriction2419_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1238912 128 Restriction2419_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
