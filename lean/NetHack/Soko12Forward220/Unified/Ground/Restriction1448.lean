import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1448_0_checked : (List.range' 741376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1448_1_checked : (List.range' 741504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1448_2_checked : (List.range' 741632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1448_3_checked : (List.range' 741760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1448_range (index : Nat) (lower : 741376 ≤ index) (upper : index < 741888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 741632 then
    if cut : index < 741504 then
      exact segment_sound _ 741376 128 Restriction1448_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 741504 128 Restriction1448_1_checked index (by omega) (by omega)
  else
    if cut : index < 741760 then
      exact segment_sound _ 741632 128 Restriction1448_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 741760 128 Restriction1448_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
