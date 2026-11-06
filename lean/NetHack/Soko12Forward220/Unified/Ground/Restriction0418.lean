import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0418_0_checked : (List.range' 214016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0418_1_checked : (List.range' 214144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0418_2_checked : (List.range' 214272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0418_3_checked : (List.range' 214400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0418_range (index : Nat) (lower : 214016 ≤ index) (upper : index < 214528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 214272 then
    if cut : index < 214144 then
      exact segment_sound _ 214016 128 Restriction0418_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 214144 128 Restriction0418_1_checked index (by omega) (by omega)
  else
    if cut : index < 214400 then
      exact segment_sound _ 214272 128 Restriction0418_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 214400 128 Restriction0418_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
