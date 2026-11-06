import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1678_0_checked : (List.range' 859136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1678_1_checked : (List.range' 859264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1678_2_checked : (List.range' 859392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1678_3_checked : (List.range' 859520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1678_range (index : Nat) (lower : 859136 ≤ index) (upper : index < 859648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 859392 then
    if cut : index < 859264 then
      exact segment_sound _ 859136 128 Restriction1678_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 859264 128 Restriction1678_1_checked index (by omega) (by omega)
  else
    if cut : index < 859520 then
      exact segment_sound _ 859392 128 Restriction1678_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 859520 128 Restriction1678_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
