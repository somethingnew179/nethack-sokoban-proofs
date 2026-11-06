import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2316_0_checked : (List.range' 1185792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2316_1_checked : (List.range' 1185920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2316_2_checked : (List.range' 1186048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2316_3_checked : (List.range' 1186176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2316_range (index : Nat) (lower : 1185792 ≤ index) (upper : index < 1186304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1186048 then
    if cut : index < 1185920 then
      exact segment_sound _ 1185792 128 Restriction2316_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1185920 128 Restriction2316_1_checked index (by omega) (by omega)
  else
    if cut : index < 1186176 then
      exact segment_sound _ 1186048 128 Restriction2316_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1186176 128 Restriction2316_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
