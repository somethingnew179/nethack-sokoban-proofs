import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1342_0_checked : (List.range' 687104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1342_1_checked : (List.range' 687232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1342_2_checked : (List.range' 687360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1342_3_checked : (List.range' 687488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1342_range (index : Nat) (lower : 687104 ≤ index) (upper : index < 687616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 687360 then
    if cut : index < 687232 then
      exact segment_sound _ 687104 128 Restriction1342_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 687232 128 Restriction1342_1_checked index (by omega) (by omega)
  else
    if cut : index < 687488 then
      exact segment_sound _ 687360 128 Restriction1342_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 687488 128 Restriction1342_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
