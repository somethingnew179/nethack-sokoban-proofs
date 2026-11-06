import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1875_0_checked : (List.range' 960000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1875_1_checked : (List.range' 960128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1875_2_checked : (List.range' 960256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1875_3_checked : (List.range' 960384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1875_range (index : Nat) (lower : 960000 ≤ index) (upper : index < 960512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 960256 then
    if cut : index < 960128 then
      exact segment_sound _ 960000 128 Restriction1875_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 960128 128 Restriction1875_1_checked index (by omega) (by omega)
  else
    if cut : index < 960384 then
      exact segment_sound _ 960256 128 Restriction1875_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 960384 128 Restriction1875_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
