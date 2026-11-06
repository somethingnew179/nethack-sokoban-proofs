import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0391_0_checked : (List.range' 200192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0391_1_checked : (List.range' 200320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0391_2_checked : (List.range' 200448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0391_3_checked : (List.range' 200576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0391_range (index : Nat) (lower : 200192 ≤ index) (upper : index < 200704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 200448 then
    if cut : index < 200320 then
      exact segment_sound _ 200192 128 Restriction0391_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 200320 128 Restriction0391_1_checked index (by omega) (by omega)
  else
    if cut : index < 200576 then
      exact segment_sound _ 200448 128 Restriction0391_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 200576 128 Restriction0391_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
