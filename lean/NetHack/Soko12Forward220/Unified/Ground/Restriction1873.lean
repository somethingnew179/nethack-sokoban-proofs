import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1873_0_checked : (List.range' 958976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1873_1_checked : (List.range' 959104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1873_2_checked : (List.range' 959232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1873_3_checked : (List.range' 959360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1873_range (index : Nat) (lower : 958976 ≤ index) (upper : index < 959488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 959232 then
    if cut : index < 959104 then
      exact segment_sound _ 958976 128 Restriction1873_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 959104 128 Restriction1873_1_checked index (by omega) (by omega)
  else
    if cut : index < 959360 then
      exact segment_sound _ 959232 128 Restriction1873_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 959360 128 Restriction1873_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
