import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1847_0_checked : (List.range' 945664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1847_1_checked : (List.range' 945792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1847_2_checked : (List.range' 945920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1847_3_checked : (List.range' 946048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1847_range (index : Nat) (lower : 945664 ≤ index) (upper : index < 946176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 945920 then
    if cut : index < 945792 then
      exact segment_sound _ 945664 128 Restriction1847_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 945792 128 Restriction1847_1_checked index (by omega) (by omega)
  else
    if cut : index < 946048 then
      exact segment_sound _ 945920 128 Restriction1847_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 946048 128 Restriction1847_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
