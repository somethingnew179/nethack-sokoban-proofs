import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0602_0_checked : (List.range' 308224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0602_1_checked : (List.range' 308352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0602_2_checked : (List.range' 308480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0602_3_checked : (List.range' 308608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0602_range (index : Nat) (lower : 308224 ≤ index) (upper : index < 308736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 308480 then
    if cut : index < 308352 then
      exact segment_sound _ 308224 128 Restriction0602_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 308352 128 Restriction0602_1_checked index (by omega) (by omega)
  else
    if cut : index < 308608 then
      exact segment_sound _ 308480 128 Restriction0602_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 308608 128 Restriction0602_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
