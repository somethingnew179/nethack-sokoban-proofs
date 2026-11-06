import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2091_0_checked : (List.range' 1070592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2091_1_checked : (List.range' 1070720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2091_2_checked : (List.range' 1070848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2091_3_checked : (List.range' 1070976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2091_range (index : Nat) (lower : 1070592 ≤ index) (upper : index < 1071104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1070848 then
    if cut : index < 1070720 then
      exact segment_sound _ 1070592 128 Restriction2091_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1070720 128 Restriction2091_1_checked index (by omega) (by omega)
  else
    if cut : index < 1070976 then
      exact segment_sound _ 1070848 128 Restriction2091_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1070976 128 Restriction2091_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
