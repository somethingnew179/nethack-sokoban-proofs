import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0727_0_checked : (List.range' 372224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0727_1_checked : (List.range' 372352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0727_2_checked : (List.range' 372480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0727_3_checked : (List.range' 372608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0727_range (index : Nat) (lower : 372224 ≤ index) (upper : index < 372736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 372480 then
    if cut : index < 372352 then
      exact segment_sound _ 372224 128 Restriction0727_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 372352 128 Restriction0727_1_checked index (by omega) (by omega)
  else
    if cut : index < 372608 then
      exact segment_sound _ 372480 128 Restriction0727_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 372608 128 Restriction0727_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
