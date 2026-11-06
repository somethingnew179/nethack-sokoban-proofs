import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1794_0_checked : (List.range' 918528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1794_1_checked : (List.range' 918656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1794_2_checked : (List.range' 918784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1794_3_checked : (List.range' 918912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1794_range (index : Nat) (lower : 918528 ≤ index) (upper : index < 919040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 918784 then
    if cut : index < 918656 then
      exact segment_sound _ 918528 128 Restriction1794_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 918656 128 Restriction1794_1_checked index (by omega) (by omega)
  else
    if cut : index < 918912 then
      exact segment_sound _ 918784 128 Restriction1794_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 918912 128 Restriction1794_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
