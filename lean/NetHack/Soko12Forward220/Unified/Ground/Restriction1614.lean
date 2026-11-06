import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1614_0_checked : (List.range' 826368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1614_1_checked : (List.range' 826496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1614_2_checked : (List.range' 826624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1614_3_checked : (List.range' 826752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1614_range (index : Nat) (lower : 826368 ≤ index) (upper : index < 826880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 826624 then
    if cut : index < 826496 then
      exact segment_sound _ 826368 128 Restriction1614_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 826496 128 Restriction1614_1_checked index (by omega) (by omega)
  else
    if cut : index < 826752 then
      exact segment_sound _ 826624 128 Restriction1614_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 826752 128 Restriction1614_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
