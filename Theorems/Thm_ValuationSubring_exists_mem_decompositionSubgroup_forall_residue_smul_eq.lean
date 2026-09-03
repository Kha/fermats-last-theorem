import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_decompositionSubgroup_forall_residue_smul_eq

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.exists_mem_decompositionSubgroup_forall_residue_smul_eq
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : ValuationSubring L)
    (φ : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A)
    (hφ : ∀ (x : K) (hx : algebraMap K L x ∈ A),
      φ (IsLocalRing.residue A ⟨algebraMap K L x, hx⟩) = IsLocalRing.residue A ⟨algebraMap K L x, hx⟩) :
    ∃ σ : L ≃ₐ[K] L, ∃ hσ : σ ∈ A.decompositionSubgroup K,
      ∀ a : A, IsLocalRing.residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • a) = φ (IsLocalRing.residue A a) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_decompositionSubgroup_forall_residue_smul_eq.solution
