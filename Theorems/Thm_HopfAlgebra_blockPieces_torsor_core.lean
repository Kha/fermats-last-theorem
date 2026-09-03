import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_TorsorGrading
import P2M.Util
import P2M.Sol.S_HopfAlgebra_blockPieces_torsor_core

set_option autoImplicit false

theorem HopfAlgebra.blockPieces_torsor_core
    (q : ℕ) [Fact q.Prime] (k : ℕ) (Λ : Type) [AddCommGroup Λ] [DecidableEq Λ] [Fintype Λ] (hΛq : ∀ g : Λ, (q ^ k) • g = 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)] [FaithfulSMul O (AlgebraicClosure ℚ)]
    (hOA : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (HO : Type) [CommRing HO] [HopfAlgebra O HO]
    [Module.Finite O HO] [Module.Flat O HO] [Coalgebra.IsCocomm O HO]
    (p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative Λ))
    (hsurj : Function.Surjective ⇑p₀)
    (e : HO) (hidem : IsIdempotentElem e)
    (hcard : Nat.card {ψ : WithConv (HO →ₐ[O] AlgebraicClosure ℚ) // ψ e = 1} = Fintype.card Λ) :
    (HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e 0 = Submodule.span O {e}) ∧
    (∀ j : Λ, ∃ t : HO, HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e j = Submodule.span O {t}) ∧
    (∀ i j : Λ, HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e (i + j) ≤
      Submodule.span O
        {z : HO | ∃ x ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e i, ∃ y ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e j, z = x * y}) ∧
    (∀ i j : Λ, ∀ x ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e i, ∀ y ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e j,
      x * y ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e (i + j)) ∧
    (∀ x : HO, x * e = x → x ∈ ⨆ j : Λ, HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e j) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_blockPieces_torsor_core.solution
