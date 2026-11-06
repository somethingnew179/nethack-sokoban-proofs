import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0917_0_checked : (List.range' 469504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0917_1_checked : (List.range' 469632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0917_2_checked : (List.range' 469760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0917_3_checked : (List.range' 469888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0917_range (index : Nat) (lower : 469504 ≤ index) (upper : index < 470016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 469760 then
    if cut : index < 469632 then
      exact segment_sound _ 469504 128 Restriction0917_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 469632 128 Restriction0917_1_checked index (by omega) (by omega)
  else
    if cut : index < 469888 then
      exact segment_sound _ 469760 128 Restriction0917_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 469888 128 Restriction0917_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
