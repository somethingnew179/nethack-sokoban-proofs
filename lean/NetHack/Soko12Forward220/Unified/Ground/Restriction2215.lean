import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2215_0_checked : (List.range' 1134080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2215_1_checked : (List.range' 1134208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2215_2_checked : (List.range' 1134336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2215_3_checked : (List.range' 1134464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2215_range (index : Nat) (lower : 1134080 ≤ index) (upper : index < 1134592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1134336 then
    if cut : index < 1134208 then
      exact segment_sound _ 1134080 128 Restriction2215_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1134208 128 Restriction2215_1_checked index (by omega) (by omega)
  else
    if cut : index < 1134464 then
      exact segment_sound _ 1134336 128 Restriction2215_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1134464 128 Restriction2215_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
