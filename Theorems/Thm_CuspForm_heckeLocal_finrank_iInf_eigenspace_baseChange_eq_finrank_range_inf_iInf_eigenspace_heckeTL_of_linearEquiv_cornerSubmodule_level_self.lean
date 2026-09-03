import Definitions.Def_CuspForm_HeckeModuleCornerRealization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.FractionRing
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_finrank_iInf_eigenspace_baseChange_eq_finrank_range_inf_iInf_eigenspace_heckeTL_of_linearEquiv_cornerSubmodule_level_self

set_option autoImplicit false

open Polynomial IsLocalRing
open scoped IsMulCommutative

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem CuspForm.heckeLocal.finrank_iInf_eigenspace_baseChange_eq_finrank_range_inf_iInf_eigenspace_heckeTL_of_linearEquiv_cornerSubmodule_level_self
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (S : Finset ℕ) (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (M : Type) [AddCommGroup M] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M] [Module 𝒪 M]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (e : M ≃ₗ[𝒪] ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)))
    (hequiv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N) (m : M),
      ((e (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) • m) :
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))) : CohCarrier.H1 N ⊤ 𝒪) =
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          CohCarrier.heckeT N ⊤ ℓ 𝒪
            ((e m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))) : CohCarrier.H1 N ⊤ 𝒪)))
    (χ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪)) :
    Module.finrank (AlgebraicClosure (FractionRing 𝒪))
      ↥(⨅ t : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ, Module.End.eigenspace
        (((LinearMap.lsmul (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M t).restrictScalars 𝒪).baseChange
          (AlgebraicClosure (FractionRing 𝒪))) (χ t)) =
    Module.finrank (AlgebraicClosure (FractionRing 𝒪))
      ↥(LinearMap.range (((IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange
          (AlgebraicClosure (FractionRing 𝒪))) ⊓
        ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N), Module.End.eigenspace
          ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 ℓ).baseChange (AlgebraicClosure (FractionRing 𝒪)))
          (χ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)))) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_finrank_iInf_eigenspace_baseChange_eq_finrank_range_inf_iInf_eigenspace_heckeTL_of_linearEquiv_cornerSubmodule_level_self.solution
