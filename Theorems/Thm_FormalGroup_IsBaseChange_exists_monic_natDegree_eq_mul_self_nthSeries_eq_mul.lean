import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsBaseChange.exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul
    (q : ℕ) (k : Type) [Field k]
    (W₀ : Type) [CommRing W₀] [IsLocalRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀]
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀))
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀) :
    ∃ (P : Polynomial (PowerSeries W₀)) (U : PowerSeries (PowerSeries W₀)),
      P.Monic ∧ P.natDegree = q * q ∧
      (∀ i : ℕ, i < q * q → P.coeff i ∈ maximalIdeal (PowerSeries W₀)) ∧
      IsUnit U ∧ Fu.nthSeries q = (P : PowerSeries (PowerSeries W₀)) * U := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul.solution
