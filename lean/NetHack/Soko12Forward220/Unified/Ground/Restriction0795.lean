import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0795_0_checked : (List.range' 407040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0795_1_checked : (List.range' 407168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0795_2_checked : (List.range' 407296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0795_3_checked : (List.range' 407424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0795_range (index : Nat) (lower : 407040 ≤ index) (upper : index < 407552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 407296 then
    if cut : index < 407168 then
      exact segment_sound _ 407040 128 Restriction0795_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 407168 128 Restriction0795_1_checked index (by omega) (by omega)
  else
    if cut : index < 407424 then
      exact segment_sound _ 407296 128 Restriction0795_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 407424 128 Restriction0795_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
