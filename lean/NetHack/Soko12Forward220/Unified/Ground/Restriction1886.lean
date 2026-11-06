import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1886_0_checked : (List.range' 965632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1886_1_checked : (List.range' 965760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1886_2_checked : (List.range' 965888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1886_3_checked : (List.range' 966016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1886_range (index : Nat) (lower : 965632 ≤ index) (upper : index < 966144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 965888 then
    if cut : index < 965760 then
      exact segment_sound _ 965632 128 Restriction1886_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 965760 128 Restriction1886_1_checked index (by omega) (by omega)
  else
    if cut : index < 966016 then
      exact segment_sound _ 965888 128 Restriction1886_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 966016 128 Restriction1886_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
