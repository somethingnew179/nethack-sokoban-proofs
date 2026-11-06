import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0438_0_checked : (List.range' 224256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0438_1_checked : (List.range' 224384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0438_2_checked : (List.range' 224512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0438_3_checked : (List.range' 224640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0438_range (index : Nat) (lower : 224256 ≤ index) (upper : index < 224768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 224512 then
    if cut : index < 224384 then
      exact segment_sound _ 224256 128 Restriction0438_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 224384 128 Restriction0438_1_checked index (by omega) (by omega)
  else
    if cut : index < 224640 then
      exact segment_sound _ 224512 128 Restriction0438_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 224640 128 Restriction0438_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
