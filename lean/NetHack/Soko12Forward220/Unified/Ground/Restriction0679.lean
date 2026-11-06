import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0679_0_checked : (List.range' 347648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0679_1_checked : (List.range' 347776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0679_2_checked : (List.range' 347904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0679_3_checked : (List.range' 348032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0679_range (index : Nat) (lower : 347648 ≤ index) (upper : index < 348160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 347904 then
    if cut : index < 347776 then
      exact segment_sound _ 347648 128 Restriction0679_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 347776 128 Restriction0679_1_checked index (by omega) (by omega)
  else
    if cut : index < 348032 then
      exact segment_sound _ 347904 128 Restriction0679_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 348032 128 Restriction0679_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
