import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0365_0_checked : (List.range' 186880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0365_1_checked : (List.range' 187008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0365_2_checked : (List.range' 187136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0365_3_checked : (List.range' 187264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0365_range (index : Nat) (lower : 186880 ≤ index) (upper : index < 187392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 187136 then
    if cut : index < 187008 then
      exact segment_sound _ 186880 128 Restriction0365_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 187008 128 Restriction0365_1_checked index (by omega) (by omega)
  else
    if cut : index < 187264 then
      exact segment_sound _ 187136 128 Restriction0365_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 187264 128 Restriction0365_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
