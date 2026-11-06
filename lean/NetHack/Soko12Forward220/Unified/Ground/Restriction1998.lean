import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1998_0_checked : (List.range' 1022976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1998_1_checked : (List.range' 1023104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1998_2_checked : (List.range' 1023232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1998_3_checked : (List.range' 1023360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1998_range (index : Nat) (lower : 1022976 ≤ index) (upper : index < 1023488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1023232 then
    if cut : index < 1023104 then
      exact segment_sound _ 1022976 128 Restriction1998_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1023104 128 Restriction1998_1_checked index (by omega) (by omega)
  else
    if cut : index < 1023360 then
      exact segment_sound _ 1023232 128 Restriction1998_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1023360 128 Restriction1998_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
