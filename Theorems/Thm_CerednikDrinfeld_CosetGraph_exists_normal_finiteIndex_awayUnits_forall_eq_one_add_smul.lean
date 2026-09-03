import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_normal_finiteIndex_awayUnits_forall_eq_one_add_smul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.exists_normal_finiteIndex_awayUnits_forall_eq_one_add_smul
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    {r : ℕ} [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r) :
    ∃ K : Subgroup ↥(CosetGraph.awayUnits R v), K.Normal ∧ K.FiniteIndex ∧
      ∀ γ : ↥(CosetGraph.awayUnits R v), γ ∈ K →
        ∃ (k : ℕ) (y : ℍ[ℚ, a, b]), ((r ^ k : ℕ) : ℚ) • y ∈ R ∧
          (((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1 + (ℓ : ℚ) • y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_normal_finiteIndex_awayUnits_forall_eq_one_add_smul.solution
