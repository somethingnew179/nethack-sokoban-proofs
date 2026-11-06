import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0205_0_checked : (List.range' 104960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0205_1_checked : (List.range' 105088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0205_2_checked : (List.range' 105216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0205_3_checked : (List.range' 105344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0205_range (index : Nat) (lower : 104960 ≤ index) (upper : index < 105472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 105216 then
    if cut : index < 105088 then
      exact segment_sound _ 104960 128 Restriction0205_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 105088 128 Restriction0205_1_checked index (by omega) (by omega)
  else
    if cut : index < 105344 then
      exact segment_sound _ 105216 128 Restriction0205_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 105344 128 Restriction0205_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
