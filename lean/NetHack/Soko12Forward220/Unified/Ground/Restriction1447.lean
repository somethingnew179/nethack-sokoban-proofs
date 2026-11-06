import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1447_0_checked : (List.range' 740864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1447_1_checked : (List.range' 740992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1447_2_checked : (List.range' 741120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1447_3_checked : (List.range' 741248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1447_range (index : Nat) (lower : 740864 ≤ index) (upper : index < 741376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 741120 then
    if cut : index < 740992 then
      exact segment_sound _ 740864 128 Restriction1447_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 740992 128 Restriction1447_1_checked index (by omega) (by omega)
  else
    if cut : index < 741248 then
      exact segment_sound _ 741120 128 Restriction1447_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 741248 128 Restriction1447_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
