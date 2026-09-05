module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Divisor_degree_eq_sum

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

end

open AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
  Finsupp.liftAddHom_apply (fun v : Place K F => AddMonoidHom.mulRight (v.deg : ℤ)) D
