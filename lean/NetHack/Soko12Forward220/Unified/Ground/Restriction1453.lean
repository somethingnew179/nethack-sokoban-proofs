import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1453_0_checked : (List.range' 743936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1453_1_checked : (List.range' 744064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1453_2_checked : (List.range' 744192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1453_3_checked : (List.range' 744320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1453_range (index : Nat) (lower : 743936 ≤ index) (upper : index < 744448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 744192 then
    if cut : index < 744064 then
      exact segment_sound _ 743936 128 Restriction1453_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 744064 128 Restriction1453_1_checked index (by omega) (by omega)
  else
    if cut : index < 744320 then
      exact segment_sound _ 744192 128 Restriction1453_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 744320 128 Restriction1453_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
