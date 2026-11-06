import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0562_0_checked : (List.range' 287744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0562_1_checked : (List.range' 287872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0562_2_checked : (List.range' 288000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0562_3_checked : (List.range' 288128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0562_range (index : Nat) (lower : 287744 ≤ index) (upper : index < 288256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 288000 then
    if cut : index < 287872 then
      exact segment_sound _ 287744 128 Restriction0562_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 287872 128 Restriction0562_1_checked index (by omega) (by omega)
  else
    if cut : index < 288128 then
      exact segment_sound _ 288000 128 Restriction0562_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 288128 128 Restriction0562_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
