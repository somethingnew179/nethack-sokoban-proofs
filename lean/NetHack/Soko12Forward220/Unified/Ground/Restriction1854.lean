import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1854_0_checked : (List.range' 949248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1854_1_checked : (List.range' 949376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1854_2_checked : (List.range' 949504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1854_3_checked : (List.range' 949632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1854_range (index : Nat) (lower : 949248 ≤ index) (upper : index < 949760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 949504 then
    if cut : index < 949376 then
      exact segment_sound _ 949248 128 Restriction1854_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 949376 128 Restriction1854_1_checked index (by omega) (by omega)
  else
    if cut : index < 949632 then
      exact segment_sound _ 949504 128 Restriction1854_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 949632 128 Restriction1854_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
