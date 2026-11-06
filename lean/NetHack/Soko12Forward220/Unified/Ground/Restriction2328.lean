import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2328_0_checked : (List.range' 1191936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2328_1_checked : (List.range' 1192064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2328_2_checked : (List.range' 1192192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2328_3_checked : (List.range' 1192320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2328_range (index : Nat) (lower : 1191936 ≤ index) (upper : index < 1192448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1192192 then
    if cut : index < 1192064 then
      exact segment_sound _ 1191936 128 Restriction2328_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1192064 128 Restriction2328_1_checked index (by omega) (by omega)
  else
    if cut : index < 1192320 then
      exact segment_sound _ 1192192 128 Restriction2328_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1192320 128 Restriction2328_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
