import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1416_0_checked : (List.range' 724992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1416_1_checked : (List.range' 725120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1416_2_checked : (List.range' 725248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1416_3_checked : (List.range' 725376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1416_range (index : Nat) (lower : 724992 ≤ index) (upper : index < 725504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 725248 then
    if cut : index < 725120 then
      exact segment_sound _ 724992 128 Restriction1416_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 725120 128 Restriction1416_1_checked index (by omega) (by omega)
  else
    if cut : index < 725376 then
      exact segment_sound _ 725248 128 Restriction1416_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 725376 128 Restriction1416_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
