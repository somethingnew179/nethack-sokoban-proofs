import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0449_0_checked : (List.range' 229888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0449_1_checked : (List.range' 230016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0449_2_checked : (List.range' 230144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0449_3_checked : (List.range' 230272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0449_range (index : Nat) (lower : 229888 ≤ index) (upper : index < 230400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 230144 then
    if cut : index < 230016 then
      exact segment_sound _ 229888 128 Restriction0449_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 230016 128 Restriction0449_1_checked index (by omega) (by omega)
  else
    if cut : index < 230272 then
      exact segment_sound _ 230144 128 Restriction0449_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 230272 128 Restriction0449_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
