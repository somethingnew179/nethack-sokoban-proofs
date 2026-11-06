import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0752_0_checked : (List.range' 385024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0752_1_checked : (List.range' 385152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0752_2_checked : (List.range' 385280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0752_3_checked : (List.range' 385408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0752_range (index : Nat) (lower : 385024 ≤ index) (upper : index < 385536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 385280 then
    if cut : index < 385152 then
      exact segment_sound _ 385024 128 Restriction0752_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 385152 128 Restriction0752_1_checked index (by omega) (by omega)
  else
    if cut : index < 385408 then
      exact segment_sound _ 385280 128 Restriction0752_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 385408 128 Restriction0752_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
