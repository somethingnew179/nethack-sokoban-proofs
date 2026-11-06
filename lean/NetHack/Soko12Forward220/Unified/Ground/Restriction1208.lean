import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1208_0_checked : (List.range' 618496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1208_1_checked : (List.range' 618624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1208_2_checked : (List.range' 618752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1208_3_checked : (List.range' 618880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1208_range (index : Nat) (lower : 618496 ≤ index) (upper : index < 619008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 618752 then
    if cut : index < 618624 then
      exact segment_sound _ 618496 128 Restriction1208_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 618624 128 Restriction1208_1_checked index (by omega) (by omega)
  else
    if cut : index < 618880 then
      exact segment_sound _ 618752 128 Restriction1208_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 618880 128 Restriction1208_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
