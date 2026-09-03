import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
namespace P2MW.S_ModularCurve_eigenIdeal_isMaximal

open ModularCurve

theorem solution {k : Type*} [Field k] [Finite k] (a : Nat.Primes → k) :
    (ModularCurve.eigenIdeal a).IsMaximal := by
  haveI : (eigenIdeal a).IsPrime := RingHom.ker_isPrime _
  haveI : Finite (HeckeAlg ⧸ eigenIdeal a) := by
    have e := RingHom.quotientKerEquivRange (R := HeckeAlg)
      (MvPolynomial.aeval (R := ℤ) a : HeckeAlg →ₐ[ℤ] k).toRingHom
    exact Finite.of_equiv _ e.symm.toEquiv
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
