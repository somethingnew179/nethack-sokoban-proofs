import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2156_0_checked : (List.range' 1103872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2156_1_checked : (List.range' 1104000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2156_2_checked : (List.range' 1104128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2156_3_checked : (List.range' 1104256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2156_range (index : Nat) (lower : 1103872 ≤ index) (upper : index < 1104384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1104128 then
    if cut : index < 1104000 then
      exact segment_sound _ 1103872 128 Restriction2156_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1104000 128 Restriction2156_1_checked index (by omega) (by omega)
  else
    if cut : index < 1104256 then
      exact segment_sound _ 1104128 128 Restriction2156_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1104256 128 Restriction2156_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
