import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1938_0_checked : (List.range' 992256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1938_1_checked : (List.range' 992384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1938_2_checked : (List.range' 992512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1938_3_checked : (List.range' 992640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1938_range (index : Nat) (lower : 992256 ≤ index) (upper : index < 992768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 992512 then
    if cut : index < 992384 then
      exact segment_sound _ 992256 128 Restriction1938_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 992384 128 Restriction1938_1_checked index (by omega) (by omega)
  else
    if cut : index < 992640 then
      exact segment_sound _ 992512 128 Restriction1938_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 992640 128 Restriction1938_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
