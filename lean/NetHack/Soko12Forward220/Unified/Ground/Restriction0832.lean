import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0832_0_checked : (List.range' 425984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0832_1_checked : (List.range' 426112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0832_2_checked : (List.range' 426240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0832_3_checked : (List.range' 426368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0832_range (index : Nat) (lower : 425984 ≤ index) (upper : index < 426496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 426240 then
    if cut : index < 426112 then
      exact segment_sound _ 425984 128 Restriction0832_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 426112 128 Restriction0832_1_checked index (by omega) (by omega)
  else
    if cut : index < 426368 then
      exact segment_sound _ 426240 128 Restriction0832_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 426368 128 Restriction0832_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
