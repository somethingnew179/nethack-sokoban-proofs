import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0652_0_checked : (List.range' 333824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0652_1_checked : (List.range' 333952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0652_2_checked : (List.range' 334080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0652_3_checked : (List.range' 334208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0652_range (index : Nat) (lower : 333824 ≤ index) (upper : index < 334336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 334080 then
    if cut : index < 333952 then
      exact segment_sound _ 333824 128 Restriction0652_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 333952 128 Restriction0652_1_checked index (by omega) (by omega)
  else
    if cut : index < 334208 then
      exact segment_sound _ 334080 128 Restriction0652_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 334208 128 Restriction0652_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
