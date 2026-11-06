import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0710_0_checked : (List.range' 363520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0710_1_checked : (List.range' 363648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0710_2_checked : (List.range' 363776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0710_3_checked : (List.range' 363904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0710_range (index : Nat) (lower : 363520 ≤ index) (upper : index < 364032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 363776 then
    if cut : index < 363648 then
      exact segment_sound _ 363520 128 Restriction0710_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 363648 128 Restriction0710_1_checked index (by omega) (by omega)
  else
    if cut : index < 363904 then
      exact segment_sound _ 363776 128 Restriction0710_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 363904 128 Restriction0710_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
