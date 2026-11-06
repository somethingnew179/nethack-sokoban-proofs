import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1501_0_checked : (List.range' 768512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1501_1_checked : (List.range' 768640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1501_2_checked : (List.range' 768768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1501_3_checked : (List.range' 768896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1501_range (index : Nat) (lower : 768512 ≤ index) (upper : index < 769024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 768768 then
    if cut : index < 768640 then
      exact segment_sound _ 768512 128 Restriction1501_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 768640 128 Restriction1501_1_checked index (by omega) (by omega)
  else
    if cut : index < 768896 then
      exact segment_sound _ 768768 128 Restriction1501_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 768896 128 Restriction1501_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
