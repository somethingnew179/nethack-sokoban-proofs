import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1021_0_checked : (List.range' 522752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1021_1_checked : (List.range' 522880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1021_2_checked : (List.range' 523008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1021_3_checked : (List.range' 523136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1021_range (index : Nat) (lower : 522752 ≤ index) (upper : index < 523264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 523008 then
    if cut : index < 522880 then
      exact segment_sound _ 522752 128 Restriction1021_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 522880 128 Restriction1021_1_checked index (by omega) (by omega)
  else
    if cut : index < 523136 then
      exact segment_sound _ 523008 128 Restriction1021_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 523136 128 Restriction1021_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
