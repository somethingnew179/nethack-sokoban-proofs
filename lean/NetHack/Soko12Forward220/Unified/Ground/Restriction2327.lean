import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2327_0_checked : (List.range' 1191424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2327_1_checked : (List.range' 1191552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2327_2_checked : (List.range' 1191680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2327_3_checked : (List.range' 1191808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2327_range (index : Nat) (lower : 1191424 ≤ index) (upper : index < 1191936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1191680 then
    if cut : index < 1191552 then
      exact segment_sound _ 1191424 128 Restriction2327_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1191552 128 Restriction2327_1_checked index (by omega) (by omega)
  else
    if cut : index < 1191808 then
      exact segment_sound _ 1191680 128 Restriction2327_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1191808 128 Restriction2327_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
