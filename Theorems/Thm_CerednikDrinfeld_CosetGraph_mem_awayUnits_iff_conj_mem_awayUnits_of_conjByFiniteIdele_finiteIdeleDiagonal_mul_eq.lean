import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_conj_mem_awayUnits_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "IsDedekindDomain NumberField QuaternionAlgebra~IsEichlerOrder CerednikDrinfeld"

theorem CerednikDrinfeld.CosetGraph.mem_awayUnits_iff_conj_mem_awayUnits_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq
    {a b : ℚ} (R R' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hR' : IsOrder R')
    (v : HeightOneSpectrum (𝓞 ℚ)) (γ₀ : (ℍ[ℚ, a, b])ˣ) (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hconj : Submodule.conjByFiniteIdele R' (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀ * g) = R) :
    ∀ x : (ℍ[ℚ, a, b])ˣ,
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R v ↔ γ₀⁻¹ * x * γ₀ ∈ CerednikDrinfeld.CosetGraph.awayUnits R' v := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_conj_mem_awayUnits_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq.solution
