import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_vdet_unitsMap_eq_padicValRat_nrd

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega ValuationSubring QuaternionAlgebra IsDedekindDomain

theorem CerednikDrinfeld.vdet_unitsMap_eq_padicValRat_nrd
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (𝒪₀ : Type) [CommRing 𝒪₀] [Algebra 𝒪₀ ↥(ratClosure A)] [IsFractionRing 𝒪₀ ↥(ratClosure A)] (π : 𝒪₀)
    (hπq : algebraMap 𝒪₀ ↥(ratClosure A) π = ((q : ℕ) : ↥(ratClosure A)))
    (h𝒪₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap 𝒪₀ ↥(ratClosure A)) ↔ Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ↥(ratClosure A) →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ↥(ratClosure A)) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪₀ˣ, (Matrix.GeneralLinearGroup.det g : ↥(ratClosure A)) = algebraMap 𝒪₀ ↥(ratClosure A) (u : 𝒪₀) * (algebraMap 𝒪₀ ↥(ratClosure A) π) ^ n)
    {a₁ b₁ : ℚ} (ι : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) (hι : Function.Injective ι)
    (x : (ℍ[ℚ, a₁, b₁])ˣ) :
    vdet (Units.map (ι : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x) =
      Multiplicative.ofAdd (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_vdet_unitsMap_eq_padicValRat_nrd.solution
