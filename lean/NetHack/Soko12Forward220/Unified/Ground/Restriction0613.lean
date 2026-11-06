import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0613_0_checked : (List.range' 313856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0613_1_checked : (List.range' 313984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0613_2_checked : (List.range' 314112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0613_3_checked : (List.range' 314240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0613_range (index : Nat) (lower : 313856 ≤ index) (upper : index < 314368) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 314112 then
    if cut : index < 313984 then
      exact segment_sound _ 313856 128 Restriction0613_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 313984 128 Restriction0613_1_checked index (by omega) (by omega)
  else
    if cut : index < 314240 then
      exact segment_sound _ 314112 128 Restriction0613_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 314240 128 Restriction0613_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
