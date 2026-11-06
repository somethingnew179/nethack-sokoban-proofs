import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2303_0_checked : (List.range' 1179136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2303_1_checked : (List.range' 1179264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2303_2_checked : (List.range' 1179392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2303_3_checked : (List.range' 1179520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2303_range (index : Nat) (lower : 1179136 ≤ index) (upper : index < 1179648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1179392 then
    if cut : index < 1179264 then
      exact segment_sound _ 1179136 128 Restriction2303_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1179264 128 Restriction2303_1_checked index (by omega) (by omega)
  else
    if cut : index < 1179520 then
      exact segment_sound _ 1179392 128 Restriction2303_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1179520 128 Restriction2303_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
