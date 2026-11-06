import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1761_0_checked : (List.range' 901632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1761_1_checked : (List.range' 901760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1761_2_checked : (List.range' 901888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1761_3_checked : (List.range' 902016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1761_range (index : Nat) (lower : 901632 ≤ index) (upper : index < 902144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 901888 then
    if cut : index < 901760 then
      exact segment_sound _ 901632 128 Restriction1761_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 901760 128 Restriction1761_1_checked index (by omega) (by omega)
  else
    if cut : index < 902016 then
      exact segment_sound _ 901888 128 Restriction1761_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 902016 128 Restriction1761_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
