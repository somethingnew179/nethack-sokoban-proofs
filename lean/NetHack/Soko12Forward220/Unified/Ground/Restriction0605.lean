import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0605_0_checked : (List.range' 309760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0605_1_checked : (List.range' 309888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0605_2_checked : (List.range' 310016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0605_3_checked : (List.range' 310144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0605_range (index : Nat) (lower : 309760 ≤ index) (upper : index < 310272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 310016 then
    if cut : index < 309888 then
      exact segment_sound _ 309760 128 Restriction0605_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 309888 128 Restriction0605_1_checked index (by omega) (by omega)
  else
    if cut : index < 310144 then
      exact segment_sound _ 310016 128 Restriction0605_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 310144 128 Restriction0605_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
