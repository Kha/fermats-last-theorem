import Definitions.Def_ModularCurve_FullLevelCuspidalSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_cuspidalSpecialization_comp_eq_tateProdRep_comp_of_laws

set_option autoImplicit false

open scoped TensorProduct
open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.cuspidalSpecialization_comp_eq_tateProdRep_comp_of_laws
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (eC : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))))
    (Op : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (h : ↥(DrinfeldCurve.hSubgroup q))
    (A : Idx q → (RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] RationalTateModule lam (jacComp q M')))
    (B : (ζ : Idx q) → (t : T) → (Y (c t) →ₗ[ℚ_[lam]] Y (c t)))
    (hEC : eC ∘ₗ Op = Op ∘ₗ eC)
    (hCOORD : ∀ ζ : Idx q, ratCoord q M' lam Ψ ζ ∘ₗ Op = A ζ ∘ₗ ratCoord q M' lam Ψ ζ)
    (hINV : ∀ (v : RationalTateModule lam (Jac q M')) (ζ : Idx q), ratCoord q M' lam Ψ ζ (eC v) ∈ Vinv)
    (hRETR : ∀ w : ↥Vinv, eInv (w : RationalTateModule lam (jacComp q M')) = w)
    (hSTAB : ∀ (ζ : Idx q) (w : RationalTateModule lam (jacComp q M')), w ∈ Vinv → A ζ w ∈ Vinv)
    (hRED : ∀ (ζ : Idx q) (t : T) (w : ↥Vinv),
      red ⟨A ζ (w : RationalTateModule lam (jacComp q M')), hSTAB ζ w w.2⟩ (c t) = B ζ t (red w (c t)))
    (hPHI : ∀ (ζ : Idx q) (t : T),
      Φ ζ t ∘ₗ B ζ t =
        ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))
            (DrinfeldCurve.drinfeldFunctionField q k ≃ₐ[k] DrinfeldCurve.drinfeldFunctionField q k)
            (DrinfeldCurve.hFunctionFieldAction q k h) ∘ₗ Φ ζ t) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ ∘ₗ Op =
      DrinfeldCurve.tateProdRep q k lam ℚ_[lam] (Idx q × T) h ∘ₗ
        cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_cuspidalSpecialization_comp_eq_tateProdRep_comp_of_laws.solution
