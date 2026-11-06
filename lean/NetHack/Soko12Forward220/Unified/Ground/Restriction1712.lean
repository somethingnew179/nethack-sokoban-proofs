import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1712_0_checked : (List.range' 876544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1712_1_checked : (List.range' 876672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1712_2_checked : (List.range' 876800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1712_3_checked : (List.range' 876928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1712_range (index : Nat) (lower : 876544 ≤ index) (upper : index < 877056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 876800 then
    if cut : index < 876672 then
      exact segment_sound _ 876544 128 Restriction1712_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 876672 128 Restriction1712_1_checked index (by omega) (by omega)
  else
    if cut : index < 876928 then
      exact segment_sound _ 876800 128 Restriction1712_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 876928 128 Restriction1712_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
