import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1012_0_checked : (List.range' 518144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1012_1_checked : (List.range' 518272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1012_2_checked : (List.range' 518400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1012_3_checked : (List.range' 518528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1012_range (index : Nat) (lower : 518144 ≤ index) (upper : index < 518656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 518400 then
    if cut : index < 518272 then
      exact segment_sound _ 518144 128 Restriction1012_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 518272 128 Restriction1012_1_checked index (by omega) (by omega)
  else
    if cut : index < 518528 then
      exact segment_sound _ 518400 128 Restriction1012_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 518528 128 Restriction1012_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
