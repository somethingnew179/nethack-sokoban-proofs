import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1891_0_checked : (List.range' 968192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1891_1_checked : (List.range' 968320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1891_2_checked : (List.range' 968448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1891_3_checked : (List.range' 968576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1891_range (index : Nat) (lower : 968192 ≤ index) (upper : index < 968704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 968448 then
    if cut : index < 968320 then
      exact segment_sound _ 968192 128 Restriction1891_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 968320 128 Restriction1891_1_checked index (by omega) (by omega)
  else
    if cut : index < 968576 then
      exact segment_sound _ 968448 128 Restriction1891_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 968576 128 Restriction1891_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
