import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2187_0_checked : (List.range' 1119744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2187_1_checked : (List.range' 1119872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2187_2_checked : (List.range' 1120000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2187_3_checked : (List.range' 1120128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2187_range (index : Nat) (lower : 1119744 ≤ index) (upper : index < 1120256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1120000 then
    if cut : index < 1119872 then
      exact segment_sound _ 1119744 128 Restriction2187_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1119872 128 Restriction2187_1_checked index (by omega) (by omega)
  else
    if cut : index < 1120128 then
      exact segment_sound _ 1120000 128 Restriction2187_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1120128 128 Restriction2187_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
