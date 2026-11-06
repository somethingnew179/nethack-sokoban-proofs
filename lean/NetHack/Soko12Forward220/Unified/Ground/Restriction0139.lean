import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0139_0_checked : (List.range' 71168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0139_1_checked : (List.range' 71296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0139_2_checked : (List.range' 71424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0139_3_checked : (List.range' 71552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0139_range (index : Nat) (lower : 71168 ≤ index) (upper : index < 71680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 71424 then
    if cut : index < 71296 then
      exact segment_sound _ 71168 128 Restriction0139_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 71296 128 Restriction0139_1_checked index (by omega) (by omega)
  else
    if cut : index < 71552 then
      exact segment_sound _ 71424 128 Restriction0139_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 71552 128 Restriction0139_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
