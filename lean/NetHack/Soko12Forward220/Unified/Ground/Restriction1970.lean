import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1970_0_checked : (List.range' 1008640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1970_1_checked : (List.range' 1008768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1970_2_checked : (List.range' 1008896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1970_3_checked : (List.range' 1009024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1970_range (index : Nat) (lower : 1008640 ≤ index) (upper : index < 1009152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1008896 then
    if cut : index < 1008768 then
      exact segment_sound _ 1008640 128 Restriction1970_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1008768 128 Restriction1970_1_checked index (by omega) (by omega)
  else
    if cut : index < 1009024 then
      exact segment_sound _ 1008896 128 Restriction1970_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1009024 128 Restriction1970_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
