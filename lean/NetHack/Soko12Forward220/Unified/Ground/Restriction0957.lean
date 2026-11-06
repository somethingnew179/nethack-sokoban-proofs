import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0957_0_checked : (List.range' 489984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0957_1_checked : (List.range' 490112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0957_2_checked : (List.range' 490240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0957_3_checked : (List.range' 490368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0957_range (index : Nat) (lower : 489984 ≤ index) (upper : index < 490496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 490240 then
    if cut : index < 490112 then
      exact segment_sound _ 489984 128 Restriction0957_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 490112 128 Restriction0957_1_checked index (by omega) (by omega)
  else
    if cut : index < 490368 then
      exact segment_sound _ 490240 128 Restriction0957_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 490368 128 Restriction0957_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
