import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0536_0_checked : (List.range' 274432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0536_1_checked : (List.range' 274560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0536_2_checked : (List.range' 274688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0536_3_checked : (List.range' 274816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0536_range (index : Nat) (lower : 274432 ≤ index) (upper : index < 274944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 274688 then
    if cut : index < 274560 then
      exact segment_sound _ 274432 128 Restriction0536_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 274560 128 Restriction0536_1_checked index (by omega) (by omega)
  else
    if cut : index < 274816 then
      exact segment_sound _ 274688 128 Restriction0536_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 274816 128 Restriction0536_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
