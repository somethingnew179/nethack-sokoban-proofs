import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2097_0_checked : (List.range' 1073664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2097_1_checked : (List.range' 1073792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2097_2_checked : (List.range' 1073920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2097_3_checked : (List.range' 1074048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2097_range (index : Nat) (lower : 1073664 ≤ index) (upper : index < 1074176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1073920 then
    if cut : index < 1073792 then
      exact segment_sound _ 1073664 128 Restriction2097_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1073792 128 Restriction2097_1_checked index (by omega) (by omega)
  else
    if cut : index < 1074048 then
      exact segment_sound _ 1073920 128 Restriction2097_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1074048 128 Restriction2097_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
