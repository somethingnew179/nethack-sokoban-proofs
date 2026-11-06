import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1059_0_checked : (List.range' 542208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1059_1_checked : (List.range' 542336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1059_2_checked : (List.range' 542464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1059_3_checked : (List.range' 542592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1059_range (index : Nat) (lower : 542208 ≤ index) (upper : index < 542720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 542464 then
    if cut : index < 542336 then
      exact segment_sound _ 542208 128 Restriction1059_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 542336 128 Restriction1059_1_checked index (by omega) (by omega)
  else
    if cut : index < 542592 then
      exact segment_sound _ 542464 128 Restriction1059_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 542592 128 Restriction1059_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
