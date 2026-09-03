import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_hopfAlgebra_surjective_ker_eq_span_nthSeries_comul_eq_adicEval_bot_of_isNilpotent

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

theorem MvFormalGroup.exists_hopfAlgebra_surjective_ker_eq_span_nthSeries_comul_eq_adicEval_bot_of_isNilpotent
    {A : Type} [CommRing A] {d : ℕ} (Φ : MvFormalGroup d A) [Φ.IsComm] (n : ℕ)
    [Module.Finite A (MvPowerSeries (Fin d) A ⧸ Ideal.span (Set.range (Φ.nthSeries n)))]
    [Module.Free A (MvPowerSeries (Fin d) A ⧸ Ideal.span (Set.range (Φ.nthSeries n)))]
    (hX : ∀ i, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.nthSeries n))) (X i))) :
    ∃ (L : Type) (_ : CommRing L) (_ : HopfAlgebra A L) (_ : Coalgebra.IsCocomm A L)
      (_ : Module.Free A L) (_ : Module.Finite A L) (π : MvPowerSeries (Fin d) A →ₐ[A] L),
      Function.Surjective π ∧
      RingHom.ker π = Ideal.span (Set.range (Φ.nthSeries n)) ∧
      Module.finrank A L =
        Module.finrank A (MvPowerSeries (Fin d) A ⧸ Ideal.span (Set.range (Φ.nthSeries n))) ∧
      (∀ i, IsNilpotent (π (X i))) ∧
      (∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (X i)) G) ∧
      (∀ i, Coalgebra.comul (R := A) (π (X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[A] L))
          (Sum.elim (fun j => π (X j) ⊗ₜ[A] (1 : L)) (fun j => (1 : L) ⊗ₜ[A] π (X j)))
          (Φ.toPowerSeries i)) ∧
      (∀ i, Coalgebra.counit (R := A) (π (X i)) = 0) ∧
      (∀ G, Coalgebra.counit (R := A) (π G) = MvPowerSeries.constantCoeff G) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_hopfAlgebra_surjective_ker_eq_span_nthSeries_comul_eq_adicEval_bot_of_isNilpotent.solution
