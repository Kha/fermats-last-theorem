import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_exists_surjective_algHom_of_dvd

theorem CuspForm.heckeLocal.exists_surjective_algHom_of_dvd
    (N N' : ℕ) [NeZero N] [NeZero N'] (hNN' : N ∣ N') (S : Set ℕ)
    (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra N' 2 S →+* IsLocalRing.ResidueField 𝒪)
    (hθ' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      θ' (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
    (hint : CuspForm.HasIntegralStructure N 2) (hint' : CuspForm.HasIntegralStructure N' 2) :
    ∃ (res : CuspForm.heckeAlgebra N' 2 S →+* CuspForm.heckeAlgebra N 2 S)
      (Ψ : CuspForm.heckeLocal N' S 𝒪 θ' →ₐ[𝒪] CuspForm.heckeLocal N S 𝒪 θ),
      θ' = θ.comp res ∧ Function.Surjective res ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        res (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS) = CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ∧
      IsLocalHom (Ψ : CuspForm.heckeLocal N' S 𝒪 θ' →+* CuspForm.heckeLocal N S 𝒪 θ) ∧
      Function.Surjective Ψ ∧
      ∀ t : CuspForm.heckeAlgebra N' 2 S,
        Ψ (CuspForm.heckeLocal.π N' S 𝒪 θ' t) = CuspForm.heckeLocal.π N S 𝒪 θ (res t) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_exists_surjective_algHom_of_dvd.solution
