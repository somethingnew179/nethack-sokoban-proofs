import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0318_0_checked : (List.range' 162816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0318_1_checked : (List.range' 162944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0318_2_checked : (List.range' 163072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0318_3_checked : (List.range' 163200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0318_range (index : Nat) (lower : 162816 ≤ index) (upper : index < 163328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 163072 then
    if cut : index < 162944 then
      exact segment_sound _ 162816 128 Restriction0318_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 162944 128 Restriction0318_1_checked index (by omega) (by omega)
  else
    if cut : index < 163200 then
      exact segment_sound _ 163072 128 Restriction0318_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 163200 128 Restriction0318_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
