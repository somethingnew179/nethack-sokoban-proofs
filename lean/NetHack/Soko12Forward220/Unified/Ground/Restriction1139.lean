import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1139_0_checked : (List.range' 583168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1139_1_checked : (List.range' 583296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1139_2_checked : (List.range' 583424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1139_3_checked : (List.range' 583552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1139_range (index : Nat) (lower : 583168 ≤ index) (upper : index < 583680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 583424 then
    if cut : index < 583296 then
      exact segment_sound _ 583168 128 Restriction1139_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 583296 128 Restriction1139_1_checked index (by omega) (by omega)
  else
    if cut : index < 583552 then
      exact segment_sound _ 583424 128 Restriction1139_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 583552 128 Restriction1139_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
