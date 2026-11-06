import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1687_0_checked : (List.range' 863744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1687_1_checked : (List.range' 863872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1687_2_checked : (List.range' 864000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1687_3_checked : (List.range' 864128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1687_range (index : Nat) (lower : 863744 ≤ index) (upper : index < 864256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 864000 then
    if cut : index < 863872 then
      exact segment_sound _ 863744 128 Restriction1687_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 863872 128 Restriction1687_1_checked index (by omega) (by omega)
  else
    if cut : index < 864128 then
      exact segment_sound _ 864000 128 Restriction1687_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 864128 128 Restriction1687_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
