import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1511_0_checked : (List.range' 773632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1511_1_checked : (List.range' 773760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1511_2_checked : (List.range' 773888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1511_3_checked : (List.range' 774016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1511_range (index : Nat) (lower : 773632 ≤ index) (upper : index < 774144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 773888 then
    if cut : index < 773760 then
      exact segment_sound _ 773632 128 Restriction1511_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 773760 128 Restriction1511_1_checked index (by omega) (by omega)
  else
    if cut : index < 774016 then
      exact segment_sound _ 773888 128 Restriction1511_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 774016 128 Restriction1511_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
