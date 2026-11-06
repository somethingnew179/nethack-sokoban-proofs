import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2387_0_checked : (List.range' 1222144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2387_1_checked : (List.range' 1222272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2387_2_checked : (List.range' 1222400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2387_3_checked : (List.range' 1222528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2387_range (index : Nat) (lower : 1222144 ≤ index) (upper : index < 1222656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1222400 then
    if cut : index < 1222272 then
      exact segment_sound _ 1222144 128 Restriction2387_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1222272 128 Restriction2387_1_checked index (by omega) (by omega)
  else
    if cut : index < 1222528 then
      exact segment_sound _ 1222400 128 Restriction2387_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1222528 128 Restriction2387_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
