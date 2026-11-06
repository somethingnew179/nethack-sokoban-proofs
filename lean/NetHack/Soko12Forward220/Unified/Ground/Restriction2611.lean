import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2611_0_checked : (List.range' 1336832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2611_1_checked : (List.range' 1336960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2611_2_checked : (List.range' 1337088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2611_3_checked : (List.range' 1337216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2611_range (index : Nat) (lower : 1336832 ≤ index) (upper : index < 1337344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1337088 then
    if cut : index < 1336960 then
      exact segment_sound _ 1336832 128 Restriction2611_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1336960 128 Restriction2611_1_checked index (by omega) (by omega)
  else
    if cut : index < 1337216 then
      exact segment_sound _ 1337088 128 Restriction2611_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1337216 128 Restriction2611_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
