import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1639_0_checked : (List.range' 839168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1639_1_checked : (List.range' 839296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1639_2_checked : (List.range' 839424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1639_3_checked : (List.range' 839552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1639_range (index : Nat) (lower : 839168 ≤ index) (upper : index < 839680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 839424 then
    if cut : index < 839296 then
      exact segment_sound _ 839168 128 Restriction1639_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 839296 128 Restriction1639_1_checked index (by omega) (by omega)
  else
    if cut : index < 839552 then
      exact segment_sound _ 839424 128 Restriction1639_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 839552 128 Restriction1639_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
