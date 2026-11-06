import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0492_0_checked : (List.range' 251904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0492_1_checked : (List.range' 252032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0492_2_checked : (List.range' 252160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0492_3_checked : (List.range' 252288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0492_range (index : Nat) (lower : 251904 ≤ index) (upper : index < 252416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 252160 then
    if cut : index < 252032 then
      exact segment_sound _ 251904 128 Restriction0492_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 252032 128 Restriction0492_1_checked index (by omega) (by omega)
  else
    if cut : index < 252288 then
      exact segment_sound _ 252160 128 Restriction0492_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 252288 128 Restriction0492_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
