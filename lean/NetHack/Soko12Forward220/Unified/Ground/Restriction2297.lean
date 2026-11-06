import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2297_0_checked : (List.range' 1176064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2297_1_checked : (List.range' 1176192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2297_2_checked : (List.range' 1176320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2297_3_checked : (List.range' 1176448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2297_range (index : Nat) (lower : 1176064 ≤ index) (upper : index < 1176576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1176320 then
    if cut : index < 1176192 then
      exact segment_sound _ 1176064 128 Restriction2297_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1176192 128 Restriction2297_1_checked index (by omega) (by omega)
  else
    if cut : index < 1176448 then
      exact segment_sound _ 1176320 128 Restriction2297_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1176448 128 Restriction2297_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
