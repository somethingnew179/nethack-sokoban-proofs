import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1688_0_checked : (List.range' 864256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1688_1_checked : (List.range' 864384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1688_2_checked : (List.range' 864512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1688_3_checked : (List.range' 864640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1688_range (index : Nat) (lower : 864256 ≤ index) (upper : index < 864768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 864512 then
    if cut : index < 864384 then
      exact segment_sound _ 864256 128 Restriction1688_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 864384 128 Restriction1688_1_checked index (by omega) (by omega)
  else
    if cut : index < 864640 then
      exact segment_sound _ 864512 128 Restriction1688_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 864640 128 Restriction1688_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
