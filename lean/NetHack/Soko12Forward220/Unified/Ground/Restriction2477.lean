import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2477_0_checked : (List.range' 1268224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2477_1_checked : (List.range' 1268352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2477_2_checked : (List.range' 1268480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2477_3_checked : (List.range' 1268608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2477_range (index : Nat) (lower : 1268224 ≤ index) (upper : index < 1268736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1268480 then
    if cut : index < 1268352 then
      exact segment_sound _ 1268224 128 Restriction2477_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1268352 128 Restriction2477_1_checked index (by omega) (by omega)
  else
    if cut : index < 1268608 then
      exact segment_sound _ 1268480 128 Restriction2477_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1268608 128 Restriction2477_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
