import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1709_0_checked : (List.range' 875008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1709_1_checked : (List.range' 875136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1709_2_checked : (List.range' 875264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1709_3_checked : (List.range' 875392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1709_range (index : Nat) (lower : 875008 ≤ index) (upper : index < 875520) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 875264 then
    if cut : index < 875136 then
      exact segment_sound _ 875008 128 Restriction1709_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 875136 128 Restriction1709_1_checked index (by omega) (by omega)
  else
    if cut : index < 875392 then
      exact segment_sound _ 875264 128 Restriction1709_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 875392 128 Restriction1709_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
