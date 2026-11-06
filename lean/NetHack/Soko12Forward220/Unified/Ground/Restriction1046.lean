import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1046_0_checked : (List.range' 535552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1046_1_checked : (List.range' 535680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1046_2_checked : (List.range' 535808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1046_3_checked : (List.range' 535936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1046_range (index : Nat) (lower : 535552 ≤ index) (upper : index < 536064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 535808 then
    if cut : index < 535680 then
      exact segment_sound _ 535552 128 Restriction1046_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 535680 128 Restriction1046_1_checked index (by omega) (by omega)
  else
    if cut : index < 535936 then
      exact segment_sound _ 535808 128 Restriction1046_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 535936 128 Restriction1046_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
