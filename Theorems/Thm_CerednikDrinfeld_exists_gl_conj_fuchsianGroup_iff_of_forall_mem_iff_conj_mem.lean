import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_gl_conj_fuchsianGroup_iff_of_forall_mem_iff_conj_mem

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_gl_conj_fuchsianGroup_iff_of_forall_mem_iff_conj_mem
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (w : (ℍ[ℚ, a, b])ˣ) (hwpos : 0 < nrd (w : ℍ[ℚ, a, b]))
    (hwnorm : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R) :
    ∃ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = ι (w : ℍ[ℚ, a, b]) ∧ 0 < g.det.val ∧
      (∀ γ : GL (Fin 2) ℝ, γ ∈ fuchsianGroup R ι ↔ g * γ * g⁻¹ ∈ fuchsianGroup R ι) ∧
      (∀ u : ℍ[ℚ, a, b], IsUnitOf R u → nrd u = 1 →
        ∃ γ : GL (Fin 2) ℝ, γ ∈ fuchsianGroup R ι ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = ι u) ∧
      (∀ x : ℍ[ℚ, a, b], nrd ((w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = nrd x) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_gl_conj_fuchsianGroup_iff_of_forall_mem_iff_conj_mem.solution
