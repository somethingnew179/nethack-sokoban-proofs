import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1344_0_checked : (List.range' 688128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1344_1_checked : (List.range' 688256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1344_2_checked : (List.range' 688384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1344_3_checked : (List.range' 688512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1344_range (index : Nat) (lower : 688128 ≤ index) (upper : index < 688640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 688384 then
    if cut : index < 688256 then
      exact segment_sound _ 688128 128 Restriction1344_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 688256 128 Restriction1344_1_checked index (by omega) (by omega)
  else
    if cut : index < 688512 then
      exact segment_sound _ 688384 128 Restriction1344_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 688512 128 Restriction1344_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
