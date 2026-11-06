import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2478_0_checked : (List.range' 1268736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2478_1_checked : (List.range' 1268864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2478_2_checked : (List.range' 1268992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2478_3_checked : (List.range' 1269120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2478_range (index : Nat) (lower : 1268736 ≤ index) (upper : index < 1269248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1268992 then
    if cut : index < 1268864 then
      exact segment_sound _ 1268736 128 Restriction2478_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1268864 128 Restriction2478_1_checked index (by omega) (by omega)
  else
    if cut : index < 1269120 then
      exact segment_sound _ 1268992 128 Restriction2478_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1269120 128 Restriction2478_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
