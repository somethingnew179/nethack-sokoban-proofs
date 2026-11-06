import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0753_0_checked : (List.range' 385536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0753_1_checked : (List.range' 385664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0753_2_checked : (List.range' 385792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0753_3_checked : (List.range' 385920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0753_range (index : Nat) (lower : 385536 ≤ index) (upper : index < 386048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 385792 then
    if cut : index < 385664 then
      exact segment_sound _ 385536 128 Restriction0753_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 385664 128 Restriction0753_1_checked index (by omega) (by omega)
  else
    if cut : index < 385920 then
      exact segment_sound _ 385792 128 Restriction0753_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 385920 128 Restriction0753_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
