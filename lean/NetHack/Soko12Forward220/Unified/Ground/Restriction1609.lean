import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1609_0_checked : (List.range' 823808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1609_1_checked : (List.range' 823936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1609_2_checked : (List.range' 824064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1609_3_checked : (List.range' 824192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1609_range (index : Nat) (lower : 823808 ≤ index) (upper : index < 824320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 824064 then
    if cut : index < 823936 then
      exact segment_sound _ 823808 128 Restriction1609_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 823936 128 Restriction1609_1_checked index (by omega) (by omega)
  else
    if cut : index < 824192 then
      exact segment_sound _ 824064 128 Restriction1609_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 824192 128 Restriction1609_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
