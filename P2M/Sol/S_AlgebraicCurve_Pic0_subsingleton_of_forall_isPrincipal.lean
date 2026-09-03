import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Pic0_subsingleton_of_forall_isPrincipal

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

end

open AlgebraicCurve in
theorem solution (K F : Type*) [Field K] [Field F] [Algebra K F]
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal) :
    Subsingleton (Pic0 K F) :=
  (QuotientAddGroup.subsingleton_iff.trans AddSubgroup.addSubgroupOf_eq_top).mpr
    fun D hD => Divisor.mem_principal.mpr (h D hD)
