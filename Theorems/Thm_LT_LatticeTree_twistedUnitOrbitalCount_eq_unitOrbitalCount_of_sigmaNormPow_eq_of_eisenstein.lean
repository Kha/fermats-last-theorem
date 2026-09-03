import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_TwistedNormClasses
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein

set_option autoImplicit false

open scoped Matrix

theorem LT.LatticeTree.twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : LT.LatticeTree.IntegralHom R K RE E) (hϖE : Irreducible (ι.toBase ϖ))
    (n : ℕ) (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : LT.LatticeTree.IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (w : Rˣ) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) (htr : ϖ ∣ Y 0 0 + Y 1 1)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E)
    (hnorm : LT.TwistedNorm.sigmaNormPow σ.mapGL n δ =
      ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ)) :
    LT.LatticeTree.twistedUnitOrbitalCount δ σ =
      LT.LatticeTree.unitOrbitalCount R (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.solution
