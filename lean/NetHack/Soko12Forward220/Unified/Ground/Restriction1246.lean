import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1246_0_checked : (List.range' 637952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1246_1_checked : (List.range' 638080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1246_2_checked : (List.range' 638208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1246_3_checked : (List.range' 638336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1246_range (index : Nat) (lower : 637952 ≤ index) (upper : index < 638464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 638208 then
    if cut : index < 638080 then
      exact segment_sound _ 637952 128 Restriction1246_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 638080 128 Restriction1246_1_checked index (by omega) (by omega)
  else
    if cut : index < 638336 then
      exact segment_sound _ 638208 128 Restriction1246_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 638336 128 Restriction1246_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
