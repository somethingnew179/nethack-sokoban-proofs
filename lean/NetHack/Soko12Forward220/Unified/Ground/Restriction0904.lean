import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0904_0_checked : (List.range' 462848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0904_1_checked : (List.range' 462976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0904_2_checked : (List.range' 463104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0904_3_checked : (List.range' 463232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0904_range (index : Nat) (lower : 462848 ≤ index) (upper : index < 463360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 463104 then
    if cut : index < 462976 then
      exact segment_sound _ 462848 128 Restriction0904_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 462976 128 Restriction0904_1_checked index (by omega) (by omega)
  else
    if cut : index < 463232 then
      exact segment_sound _ 463104 128 Restriction0904_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 463232 128 Restriction0904_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
