import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2020_0_checked : (List.range' 1034240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2020_1_checked : (List.range' 1034368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2020_2_checked : (List.range' 1034496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2020_3_checked : (List.range' 1034624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2020_range (index : Nat) (lower : 1034240 ≤ index) (upper : index < 1034752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1034496 then
    if cut : index < 1034368 then
      exact segment_sound _ 1034240 128 Restriction2020_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1034368 128 Restriction2020_1_checked index (by omega) (by omega)
  else
    if cut : index < 1034624 then
      exact segment_sound _ 1034496 128 Restriction2020_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1034624 128 Restriction2020_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
