import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0912_0_checked : (List.range' 466944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0912_1_checked : (List.range' 467072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0912_2_checked : (List.range' 467200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0912_3_checked : (List.range' 467328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0912_range (index : Nat) (lower : 466944 ≤ index) (upper : index < 467456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 467200 then
    if cut : index < 467072 then
      exact segment_sound _ 466944 128 Restriction0912_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 467072 128 Restriction0912_1_checked index (by omega) (by omega)
  else
    if cut : index < 467328 then
      exact segment_sound _ 467200 128 Restriction0912_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 467328 128 Restriction0912_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
