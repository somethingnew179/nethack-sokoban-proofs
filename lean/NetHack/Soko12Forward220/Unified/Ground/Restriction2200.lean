import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2200_0_checked : (List.range' 1126400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2200_1_checked : (List.range' 1126528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2200_2_checked : (List.range' 1126656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2200_3_checked : (List.range' 1126784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2200_range (index : Nat) (lower : 1126400 ≤ index) (upper : index < 1126912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1126656 then
    if cut : index < 1126528 then
      exact segment_sound _ 1126400 128 Restriction2200_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1126528 128 Restriction2200_1_checked index (by omega) (by omega)
  else
    if cut : index < 1126784 then
      exact segment_sound _ 1126656 128 Restriction2200_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1126784 128 Restriction2200_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
