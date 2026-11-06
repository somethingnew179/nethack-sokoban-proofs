import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1217_0_checked : (List.range' 623104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1217_1_checked : (List.range' 623232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1217_2_checked : (List.range' 623360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1217_3_checked : (List.range' 623488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1217_range (index : Nat) (lower : 623104 ≤ index) (upper : index < 623616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 623360 then
    if cut : index < 623232 then
      exact segment_sound _ 623104 128 Restriction1217_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 623232 128 Restriction1217_1_checked index (by omega) (by omega)
  else
    if cut : index < 623488 then
      exact segment_sound _ 623360 128 Restriction1217_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 623488 128 Restriction1217_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
