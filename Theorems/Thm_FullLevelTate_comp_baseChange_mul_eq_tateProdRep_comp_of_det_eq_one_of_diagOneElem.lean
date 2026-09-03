import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_FullLevelTate_comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime]
    (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    (I : Type)
    (sp : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
      DrinfeldCurve.tateProd q k lam ℚ_[lam] I)
    (hlevel : ∀ h : DrinfeldCurve.hSubgroup q,
      ((h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 = 1) →
        sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam
            (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1).baseChange ℚ_[lam] =
          DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I h ∘ₗ sp)
    (hinert : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ h : DrinfeldCurve.hSubgroup q,
      ι ((h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 : GaloisField q 2) =
          P.tameCharacter π τ →
        (∃ e : (ZMod q)ˣ, (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 =
          ModularCurve.FullLevel.diagOneElem q e) →
        sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam
              (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 *
            ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
          DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I h ∘ₗ sp) :
    ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
      ι (α : GaloisField q 2) = P.tameCharacter π τ →
        ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
          sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g *
              ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
            DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(g, α), hg⟩ ∘ₗ sp := by p2m_exact_reverting @_root_.P2MW.S_FullLevelTate_comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem.solution
