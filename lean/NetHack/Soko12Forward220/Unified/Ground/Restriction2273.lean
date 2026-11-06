import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2273_0_checked : (List.range' 1163776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2273_1_checked : (List.range' 1163904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2273_2_checked : (List.range' 1164032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2273_3_checked : (List.range' 1164160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2273_range (index : Nat) (lower : 1163776 ≤ index) (upper : index < 1164288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1164032 then
    if cut : index < 1163904 then
      exact segment_sound _ 1163776 128 Restriction2273_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1163904 128 Restriction2273_1_checked index (by omega) (by omega)
  else
    if cut : index < 1164160 then
      exact segment_sound _ 1164032 128 Restriction2273_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1164160 128 Restriction2273_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
