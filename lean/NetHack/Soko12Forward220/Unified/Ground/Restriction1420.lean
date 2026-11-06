import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1420_0_checked : (List.range' 727040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1420_1_checked : (List.range' 727168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1420_2_checked : (List.range' 727296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1420_3_checked : (List.range' 727424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1420_range (index : Nat) (lower : 727040 ≤ index) (upper : index < 727552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 727296 then
    if cut : index < 727168 then
      exact segment_sound _ 727040 128 Restriction1420_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 727168 128 Restriction1420_1_checked index (by omega) (by omega)
  else
    if cut : index < 727424 then
      exact segment_sound _ 727296 128 Restriction1420_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 727424 128 Restriction1420_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
