import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0923_0_checked : (List.range' 472576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0923_1_checked : (List.range' 472704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0923_2_checked : (List.range' 472832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0923_3_checked : (List.range' 472960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0923_range (index : Nat) (lower : 472576 ≤ index) (upper : index < 473088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 472832 then
    if cut : index < 472704 then
      exact segment_sound _ 472576 128 Restriction0923_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 472704 128 Restriction0923_1_checked index (by omega) (by omega)
  else
    if cut : index < 472960 then
      exact segment_sound _ 472832 128 Restriction0923_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 472960 128 Restriction0923_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
