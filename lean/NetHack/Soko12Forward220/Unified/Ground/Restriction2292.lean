import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2292_0_checked : (List.range' 1173504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2292_1_checked : (List.range' 1173632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2292_2_checked : (List.range' 1173760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2292_3_checked : (List.range' 1173888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2292_range (index : Nat) (lower : 1173504 ≤ index) (upper : index < 1174016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1173760 then
    if cut : index < 1173632 then
      exact segment_sound _ 1173504 128 Restriction2292_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1173632 128 Restriction2292_1_checked index (by omega) (by omega)
  else
    if cut : index < 1173888 then
      exact segment_sound _ 1173760 128 Restriction2292_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1173888 128 Restriction2292_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
