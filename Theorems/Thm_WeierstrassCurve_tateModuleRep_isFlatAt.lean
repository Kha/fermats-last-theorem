import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_tateModuleRep_isFlatAt

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve.Affine.Point in
theorem WeierstrassCurve.tateModuleRep_isFlatAt
    (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) =
        (p ^ n) ^ 2)
    (hprol :
      ∀ n : ℕ, 0 < n →
        ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
          Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
          Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
          Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
          ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
              Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ),
            (∀ f g, e (f * g) = e f + e g) ∧
            ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
              (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
              (∀ h : H, g h = σ (f h)) → e g = σ • (e f)) :
    (W.tateModuleRep p hcard).IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_tateModuleRep_isFlatAt.solution
