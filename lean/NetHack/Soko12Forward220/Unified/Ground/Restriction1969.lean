import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1969_0_checked : (List.range' 1008128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1969_1_checked : (List.range' 1008256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1969_2_checked : (List.range' 1008384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1969_3_checked : (List.range' 1008512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1969_range (index : Nat) (lower : 1008128 ≤ index) (upper : index < 1008640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1008384 then
    if cut : index < 1008256 then
      exact segment_sound _ 1008128 128 Restriction1969_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1008256 128 Restriction1969_1_checked index (by omega) (by omega)
  else
    if cut : index < 1008512 then
      exact segment_sound _ 1008384 128 Restriction1969_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1008512 128 Restriction1969_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
