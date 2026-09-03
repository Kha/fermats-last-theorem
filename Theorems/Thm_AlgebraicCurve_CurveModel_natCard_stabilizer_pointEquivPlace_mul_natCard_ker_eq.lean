import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_natCard_stabilizer_pointEquivPlace_mul_natCard_ker_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.natCard_stabilizer_pointEquivPlace_mul_natCard_ker_eq
    {k : Type u} [Field k] [IsAlgClosed k] {L : Type v} [Field L] [Algebra k L]
    (M : CurveModel k L)
    (F : Type v) [Field F] [Algebra k F] [Algebra F L] [IsScalarTower k F L] [FiniteDimensional F L]
    (G₀ : Type u) [Group G₀] [Finite G₀] (ρ : G₀ →* Aut M.C) (hρ : ∀ g : G₀, (ρ g).hom ≫ M.toBase = M.toBase)
    (θ : G₀ →* (L ≃ₐ[F] L)) (hθsurj : Function.Surjective θ)
    (hθ : ∀ (g : G₀) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((ρ g).inv ⁻¹ᵁ U))] (f : Γ(M.C, U)),
        θ g (M.ffEquiv.symm (M.C.germToFunctionField U f)) =
          M.ffEquiv.symm (M.C.germToFunctionField ((ρ g).inv ⁻¹ᵁ U) ((ρ g).inv.app U f)))
    (hθker : ∀ g : G₀, θ g = 1 ↔ ρ g = 1)
    (x : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    Nat.card {σ : L ≃ₐ[F] L // SemilinearAut.ofAlgAut (σ.restrictScalars k) • M.pointEquivPlace x = M.pointEquivPlace x} *
        Nat.card θ.ker =
      Nat.card {g : G₀ // x.1 ≫ (ρ g).hom = x.1} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_natCard_stabilizer_pointEquivPlace_mul_natCard_ker_eq.solution
