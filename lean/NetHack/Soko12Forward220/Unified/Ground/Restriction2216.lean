import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2216_0_checked : (List.range' 1134592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2216_1_checked : (List.range' 1134720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2216_2_checked : (List.range' 1134848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2216_3_checked : (List.range' 1134976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2216_range (index : Nat) (lower : 1134592 ≤ index) (upper : index < 1135104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1134848 then
    if cut : index < 1134720 then
      exact segment_sound _ 1134592 128 Restriction2216_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1134720 128 Restriction2216_1_checked index (by omega) (by omega)
  else
    if cut : index < 1134976 then
      exact segment_sound _ 1134848 128 Restriction2216_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1134976 128 Restriction2216_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
