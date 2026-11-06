import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2359_0_checked : (List.range' 1207808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2359_1_checked : (List.range' 1207936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2359_2_checked : (List.range' 1208064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2359_3_checked : (List.range' 1208192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2359_range (index : Nat) (lower : 1207808 ≤ index) (upper : index < 1208320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1208064 then
    if cut : index < 1207936 then
      exact segment_sound _ 1207808 128 Restriction2359_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1207936 128 Restriction2359_1_checked index (by omega) (by omega)
  else
    if cut : index < 1208192 then
      exact segment_sound _ 1208064 128 Restriction2359_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1208192 128 Restriction2359_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
