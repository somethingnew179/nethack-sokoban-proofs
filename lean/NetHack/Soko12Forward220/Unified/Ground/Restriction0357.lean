import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0357_0_checked : (List.range' 182784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0357_1_checked : (List.range' 182912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0357_2_checked : (List.range' 183040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0357_3_checked : (List.range' 183168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0357_range (index : Nat) (lower : 182784 ≤ index) (upper : index < 183296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 183040 then
    if cut : index < 182912 then
      exact segment_sound _ 182784 128 Restriction0357_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 182912 128 Restriction0357_1_checked index (by omega) (by omega)
  else
    if cut : index < 183168 then
      exact segment_sound _ 183040 128 Restriction0357_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 183168 128 Restriction0357_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
