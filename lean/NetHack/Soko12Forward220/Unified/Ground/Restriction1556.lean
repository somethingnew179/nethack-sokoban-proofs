import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1556_0_checked : (List.range' 796672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1556_1_checked : (List.range' 796800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1556_2_checked : (List.range' 796928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1556_3_checked : (List.range' 797056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1556_range (index : Nat) (lower : 796672 ≤ index) (upper : index < 797184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 796928 then
    if cut : index < 796800 then
      exact segment_sound _ 796672 128 Restriction1556_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 796800 128 Restriction1556_1_checked index (by omega) (by omega)
  else
    if cut : index < 797056 then
      exact segment_sound _ 796928 128 Restriction1556_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 797056 128 Restriction1556_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
