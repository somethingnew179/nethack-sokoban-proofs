import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2353_0_checked : (List.range' 1204736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2353_1_checked : (List.range' 1204864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2353_2_checked : (List.range' 1204992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2353_3_checked : (List.range' 1205120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2353_range (index : Nat) (lower : 1204736 ≤ index) (upper : index < 1205248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1204992 then
    if cut : index < 1204864 then
      exact segment_sound _ 1204736 128 Restriction2353_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1204864 128 Restriction2353_1_checked index (by omega) (by omega)
  else
    if cut : index < 1205120 then
      exact segment_sound _ 1204992 128 Restriction2353_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1205120 128 Restriction2353_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
