import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1521_0_checked : (List.range' 778752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1521_1_checked : (List.range' 778880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1521_2_checked : (List.range' 779008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1521_3_checked : (List.range' 779136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1521_range (index : Nat) (lower : 778752 ≤ index) (upper : index < 779264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 779008 then
    if cut : index < 778880 then
      exact segment_sound _ 778752 128 Restriction1521_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 778880 128 Restriction1521_1_checked index (by omega) (by omega)
  else
    if cut : index < 779136 then
      exact segment_sound _ 779008 128 Restriction1521_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 779136 128 Restriction1521_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
