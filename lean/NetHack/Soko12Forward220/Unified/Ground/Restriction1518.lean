import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1518_0_checked : (List.range' 777216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1518_1_checked : (List.range' 777344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1518_2_checked : (List.range' 777472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1518_3_checked : (List.range' 777600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1518_range (index : Nat) (lower : 777216 ≤ index) (upper : index < 777728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 777472 then
    if cut : index < 777344 then
      exact segment_sound _ 777216 128 Restriction1518_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 777344 128 Restriction1518_1_checked index (by omega) (by omega)
  else
    if cut : index < 777600 then
      exact segment_sound _ 777472 128 Restriction1518_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 777600 128 Restriction1518_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
