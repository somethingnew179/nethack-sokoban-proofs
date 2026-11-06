import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1205_0_checked : (List.range' 616960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1205_1_checked : (List.range' 617088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1205_2_checked : (List.range' 617216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1205_3_checked : (List.range' 617344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1205_range (index : Nat) (lower : 616960 ≤ index) (upper : index < 617472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 617216 then
    if cut : index < 617088 then
      exact segment_sound _ 616960 128 Restriction1205_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 617088 128 Restriction1205_1_checked index (by omega) (by omega)
  else
    if cut : index < 617344 then
      exact segment_sound _ 617216 128 Restriction1205_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 617344 128 Restriction1205_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
