import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1699_0_checked : (List.range' 869888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1699_1_checked : (List.range' 870016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1699_2_checked : (List.range' 870144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1699_3_checked : (List.range' 870272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1699_range (index : Nat) (lower : 869888 ≤ index) (upper : index < 870400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 870144 then
    if cut : index < 870016 then
      exact segment_sound _ 869888 128 Restriction1699_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 870016 128 Restriction1699_1_checked index (by omega) (by omega)
  else
    if cut : index < 870272 then
      exact segment_sound _ 870144 128 Restriction1699_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 870272 128 Restriction1699_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
