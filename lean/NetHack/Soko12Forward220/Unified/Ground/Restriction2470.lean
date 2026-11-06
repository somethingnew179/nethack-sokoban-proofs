import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2470_0_checked : (List.range' 1264640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2470_1_checked : (List.range' 1264768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2470_2_checked : (List.range' 1264896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2470_3_checked : (List.range' 1265024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2470_range (index : Nat) (lower : 1264640 ≤ index) (upper : index < 1265152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1264896 then
    if cut : index < 1264768 then
      exact segment_sound _ 1264640 128 Restriction2470_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1264768 128 Restriction2470_1_checked index (by omega) (by omega)
  else
    if cut : index < 1265024 then
      exact segment_sound _ 1264896 128 Restriction2470_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1265024 128 Restriction2470_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
