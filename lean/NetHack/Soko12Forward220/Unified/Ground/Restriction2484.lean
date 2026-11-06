import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2484_0_checked : (List.range' 1271808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2484_1_checked : (List.range' 1271936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2484_2_checked : (List.range' 1272064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2484_3_checked : (List.range' 1272192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2484_range (index : Nat) (lower : 1271808 ≤ index) (upper : index < 1272320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1272064 then
    if cut : index < 1271936 then
      exact segment_sound _ 1271808 128 Restriction2484_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1271936 128 Restriction2484_1_checked index (by omega) (by omega)
  else
    if cut : index < 1272192 then
      exact segment_sound _ 1272064 128 Restriction2484_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1272192 128 Restriction2484_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
