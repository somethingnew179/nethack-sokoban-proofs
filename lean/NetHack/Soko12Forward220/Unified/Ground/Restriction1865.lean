import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1865_0_checked : (List.range' 954880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1865_1_checked : (List.range' 955008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1865_2_checked : (List.range' 955136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1865_3_checked : (List.range' 955264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1865_range (index : Nat) (lower : 954880 ≤ index) (upper : index < 955392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 955136 then
    if cut : index < 955008 then
      exact segment_sound _ 954880 128 Restriction1865_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 955008 128 Restriction1865_1_checked index (by omega) (by omega)
  else
    if cut : index < 955264 then
      exact segment_sound _ 955136 128 Restriction1865_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 955264 128 Restriction1865_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
