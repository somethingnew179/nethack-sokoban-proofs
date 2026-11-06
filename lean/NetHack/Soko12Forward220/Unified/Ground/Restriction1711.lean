import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1711_0_checked : (List.range' 876032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1711_1_checked : (List.range' 876160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1711_2_checked : (List.range' 876288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1711_3_checked : (List.range' 876416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1711_range (index : Nat) (lower : 876032 ≤ index) (upper : index < 876544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 876288 then
    if cut : index < 876160 then
      exact segment_sound _ 876032 128 Restriction1711_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 876160 128 Restriction1711_1_checked index (by omega) (by omega)
  else
    if cut : index < 876416 then
      exact segment_sound _ 876288 128 Restriction1711_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 876416 128 Restriction1711_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
