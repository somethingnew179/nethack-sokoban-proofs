import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0773_0_checked : (List.range' 395776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0773_1_checked : (List.range' 395904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0773_2_checked : (List.range' 396032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0773_3_checked : (List.range' 396160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0773_range (index : Nat) (lower : 395776 ≤ index) (upper : index < 396288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 396032 then
    if cut : index < 395904 then
      exact segment_sound _ 395776 128 Restriction0773_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 395904 128 Restriction0773_1_checked index (by omega) (by omega)
  else
    if cut : index < 396160 then
      exact segment_sound _ 396032 128 Restriction0773_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 396160 128 Restriction0773_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
