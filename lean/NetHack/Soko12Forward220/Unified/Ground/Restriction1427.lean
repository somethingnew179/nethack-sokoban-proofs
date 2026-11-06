import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1427_0_checked : (List.range' 730624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1427_1_checked : (List.range' 730752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1427_2_checked : (List.range' 730880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1427_3_checked : (List.range' 731008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1427_range (index : Nat) (lower : 730624 ≤ index) (upper : index < 731136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 730880 then
    if cut : index < 730752 then
      exact segment_sound _ 730624 128 Restriction1427_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 730752 128 Restriction1427_1_checked index (by omega) (by omega)
  else
    if cut : index < 731008 then
      exact segment_sound _ 730880 128 Restriction1427_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 731008 128 Restriction1427_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
