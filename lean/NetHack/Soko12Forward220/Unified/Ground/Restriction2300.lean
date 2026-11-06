import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2300_0_checked : (List.range' 1177600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2300_1_checked : (List.range' 1177728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2300_2_checked : (List.range' 1177856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2300_3_checked : (List.range' 1177984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2300_range (index : Nat) (lower : 1177600 ≤ index) (upper : index < 1178112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1177856 then
    if cut : index < 1177728 then
      exact segment_sound _ 1177600 128 Restriction2300_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1177728 128 Restriction2300_1_checked index (by omega) (by omega)
  else
    if cut : index < 1177984 then
      exact segment_sound _ 1177856 128 Restriction2300_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1177984 128 Restriction2300_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
