import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0002_0_checked : (List.range' 1024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0002_1_checked : (List.range' 1152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0002_2_checked : (List.range' 1280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0002_3_checked : (List.range' 1408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0002_range (index : Nat) (lower : 1024 ≤ index) (upper : index < 1536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1280 then
    if cut : index < 1152 then
      exact segment_sound _ 1024 128 Restriction0002_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1152 128 Restriction0002_1_checked index (by omega) (by omega)
  else
    if cut : index < 1408 then
      exact segment_sound _ 1280 128 Restriction0002_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1408 128 Restriction0002_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
