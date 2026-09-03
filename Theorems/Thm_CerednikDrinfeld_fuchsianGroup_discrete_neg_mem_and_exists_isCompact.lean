import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_fuchsianGroup_discrete_neg_mem_and_exists_isCompact

set_option autoImplicit false

open scoped MatrixGroups Topology Quaternion
open QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.fuchsianGroup_discrete_neg_mem_and_exists_isCompact
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    (∀ γ ∈ fuchsianGroup R ι, Matrix.GeneralLinearGroup.det γ = 1) ∧
    (-1 ∈ fuchsianGroup R ι) ∧
    DiscreteTopology ↥(fuchsianGroup R ι) ∧
    (∃ K : Set UpperHalfPlane, IsCompact K ∧ ∀ τ : UpperHalfPlane, ∃ γ ∈ fuchsianGroup R ι, γ • τ ∈ K) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_fuchsianGroup_discrete_neg_mem_and_exists_isCompact.solution
