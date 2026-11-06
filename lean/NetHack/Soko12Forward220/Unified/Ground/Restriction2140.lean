import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2140_0_checked : (List.range' 1095680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2140_1_checked : (List.range' 1095808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2140_2_checked : (List.range' 1095936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2140_3_checked : (List.range' 1096064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2140_range (index : Nat) (lower : 1095680 ≤ index) (upper : index < 1096192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1095936 then
    if cut : index < 1095808 then
      exact segment_sound _ 1095680 128 Restriction2140_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1095808 128 Restriction2140_1_checked index (by omega) (by omega)
  else
    if cut : index < 1096064 then
      exact segment_sound _ 1095936 128 Restriction2140_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1096064 128 Restriction2140_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
