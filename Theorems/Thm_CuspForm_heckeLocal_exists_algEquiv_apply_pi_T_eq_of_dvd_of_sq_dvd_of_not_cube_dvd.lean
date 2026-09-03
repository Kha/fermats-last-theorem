import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_CohCarrier_Tower
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_exists_algEquiv_apply_pi_T_eq_of_dvd_of_sq_dvd_of_not_cube_dvd

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeLocal.exists_algEquiv_apply_pi_T_eq_of_dvd_of_sq_dvd_of_not_cube_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (hirr : ρbar.IsIrreducible)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)

    (M M' : ℕ) [NeZero M] [NeZero M'] (hMM' : M ∣ M')
    (hM'S : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)

    (hsat : ∀ q : ℕ, q.Prime → q ∣ M' → q ≠ p → (q ^ 2 ∣ M ∨ ∀ n : ℕ, q ^ n ∣ M' → q ^ n ∣ M))

    (hM'3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M')

    (hpM : ∀ k : ℕ, p ^ k ∣ M' → p ^ k ∣ M)

    (hram : ∀ q : ℕ, q.Prime → q ∣ M' → q ≠ p →
      ρbar.IsUnramifiedAt q ∨ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    [Fact (CuspForm.HasIntegralStructure M 2)] [Fact (CuspForm.HasIntegralStructure M' 2)]

    (θ : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra M' 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθθ' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
      θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS) =
        θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS))
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X + C (ℓ : ResidueField 𝒪)) :
    ∃ e : CuspForm.heckeLocal M' (↑S : Set ℕ) 𝒪 θ' ≃ₐ[𝒪] CuspForm.heckeLocal M (↑S : Set ℕ) 𝒪 θ,
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
        e (CuspForm.heckeLocal.π M' (↑S : Set ℕ) 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS)) =
          CuspForm.heckeLocal.π M (↑S : Set ℕ) 𝒪 θ
            (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_exists_algEquiv_apply_pi_T_eq_of_dvd_of_sq_dvd_of_not_cube_dvd.solution
