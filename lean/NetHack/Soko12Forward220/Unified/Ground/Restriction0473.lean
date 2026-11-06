import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0473_0_checked : (List.range' 242176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0473_1_checked : (List.range' 242304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0473_2_checked : (List.range' 242432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0473_3_checked : (List.range' 242560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0473_range (index : Nat) (lower : 242176 ≤ index) (upper : index < 242688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 242432 then
    if cut : index < 242304 then
      exact segment_sound _ 242176 128 Restriction0473_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 242304 128 Restriction0473_1_checked index (by omega) (by omega)
  else
    if cut : index < 242560 then
      exact segment_sound _ 242432 128 Restriction0473_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 242560 128 Restriction0473_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
