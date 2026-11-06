import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0142_0_checked : (List.range' 72704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0142_1_checked : (List.range' 72832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0142_2_checked : (List.range' 72960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0142_3_checked : (List.range' 73088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0142_range (index : Nat) (lower : 72704 ≤ index) (upper : index < 73216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 72960 then
    if cut : index < 72832 then
      exact segment_sound _ 72704 128 Restriction0142_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 72832 128 Restriction0142_1_checked index (by omega) (by omega)
  else
    if cut : index < 73088 then
      exact segment_sound _ 72960 128 Restriction0142_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 73088 128 Restriction0142_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
