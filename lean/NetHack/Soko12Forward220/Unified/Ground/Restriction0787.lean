import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0787_0_checked : (List.range' 402944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0787_1_checked : (List.range' 403072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0787_2_checked : (List.range' 403200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0787_3_checked : (List.range' 403328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0787_range (index : Nat) (lower : 402944 ≤ index) (upper : index < 403456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 403200 then
    if cut : index < 403072 then
      exact segment_sound _ 402944 128 Restriction0787_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 403072 128 Restriction0787_1_checked index (by omega) (by omega)
  else
    if cut : index < 403328 then
      exact segment_sound _ 403200 128 Restriction0787_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 403328 128 Restriction0787_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
