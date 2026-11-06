import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1689_0_checked : (List.range' 864768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1689_1_checked : (List.range' 864896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1689_2_checked : (List.range' 865024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1689_3_checked : (List.range' 865152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1689_range (index : Nat) (lower : 864768 ≤ index) (upper : index < 865280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 865024 then
    if cut : index < 864896 then
      exact segment_sound _ 864768 128 Restriction1689_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 864896 128 Restriction1689_1_checked index (by omega) (by omega)
  else
    if cut : index < 865152 then
      exact segment_sound _ 865024 128 Restriction1689_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 865152 128 Restriction1689_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
