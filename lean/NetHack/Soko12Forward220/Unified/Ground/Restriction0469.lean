import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0469_0_checked : (List.range' 240128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0469_1_checked : (List.range' 240256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0469_2_checked : (List.range' 240384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0469_3_checked : (List.range' 240512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0469_range (index : Nat) (lower : 240128 ≤ index) (upper : index < 240640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 240384 then
    if cut : index < 240256 then
      exact segment_sound _ 240128 128 Restriction0469_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 240256 128 Restriction0469_1_checked index (by omega) (by omega)
  else
    if cut : index < 240512 then
      exact segment_sound _ 240384 128 Restriction0469_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 240512 128 Restriction0469_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
