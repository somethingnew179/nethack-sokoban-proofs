import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0823_0_checked : (List.range' 421376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0823_1_checked : (List.range' 421504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0823_2_checked : (List.range' 421632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0823_3_checked : (List.range' 421760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0823_range (index : Nat) (lower : 421376 ≤ index) (upper : index < 421888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 421632 then
    if cut : index < 421504 then
      exact segment_sound _ 421376 128 Restriction0823_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 421504 128 Restriction0823_1_checked index (by omega) (by omega)
  else
    if cut : index < 421760 then
      exact segment_sound _ 421632 128 Restriction0823_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 421760 128 Restriction0823_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
