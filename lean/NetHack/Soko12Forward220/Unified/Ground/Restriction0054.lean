import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0054_0_checked : (List.range' 27648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0054_1_checked : (List.range' 27776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0054_2_checked : (List.range' 27904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0054_3_checked : (List.range' 28032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0054_range (index : Nat) (lower : 27648 ≤ index) (upper : index < 28160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 27904 then
    if cut : index < 27776 then
      exact segment_sound _ 27648 128 Restriction0054_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 27776 128 Restriction0054_1_checked index (by omega) (by omega)
  else
    if cut : index < 28032 then
      exact segment_sound _ 27904 128 Restriction0054_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 28032 128 Restriction0054_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
