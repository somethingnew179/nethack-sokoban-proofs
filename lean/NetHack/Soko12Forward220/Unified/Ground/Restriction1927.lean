import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1927_0_checked : (List.range' 986624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1927_1_checked : (List.range' 986752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1927_2_checked : (List.range' 986880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1927_3_checked : (List.range' 987008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1927_range (index : Nat) (lower : 986624 ≤ index) (upper : index < 987136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 986880 then
    if cut : index < 986752 then
      exact segment_sound _ 986624 128 Restriction1927_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 986752 128 Restriction1927_1_checked index (by omega) (by omega)
  else
    if cut : index < 987008 then
      exact segment_sound _ 986880 128 Restriction1927_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 987008 128 Restriction1927_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
