import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_PadicAlgCl_smul_kummerCocycle_pairing_mem_levelCoboundaries2_of_thickening

set_option autoImplicit false
theorem PadicAlgCl.smul_kummerCocycle_pairing_mem_levelCoboundaries2_of_thickening
    {B : Type} [CommRing B] [IsLocalRing B] (p N : ℕ) [Fact p.Prime] (hN : 1 ≤ N)
    (hNB : (p : B) ^ N = 0)
    (x z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ) (y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : FiniteDimensional ℚ F)
    (hxmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), x (g * h) = x g * x h)
    (hzmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z (g * h) = z g * z h)
    (hy : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), y (g * h) = (x g : B) * y h + y g * (z h : B))
    (hlev : ∀ s : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), localGaloisToGlobal p s ∈ F.fixingSubgroup → x s = 1 ∧ y s = 0 ∧ z s = 1)
    (hxz : ∀ (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (a : ℕ), (∀ μ : PadicAlgCl p, μ ^ p ^ N = 1 → g μ = μ ^ a) →
      (x g : B) * (z g : B) - (a : B) ∈ Ideal.span {((p ^ N : ℕ) : B)})
    (t η : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0)
    (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℤ) (hχz : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) = 1 + t * η * (χ g : B))
    (ζ : PadicAlgCl p) (hζ : IsPrimitiveRoot ζ p)
    (Λ : IsLocalRing.ResidueField B →+ ZMod p) (π : B →+ ZMod (p ^ N))
    (hπ : ∀ c : B, π (t * c) = ((Λ (IsLocalRing.residue B c)).val : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ (N - 1))
    (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ)
    (hα : algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p)
    (hrep : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), g (α : PadicAlgCl p) =
          ζ ^ (Λ (IsLocalRing.residue B (η * (y g * (((z g)⁻¹ : Bˣ) : B))))).val * (α : PadicAlgCl p)) :
    (fun g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) × (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) =>
        (MonoidHom.toAdditive (rootsOfUnity p (PadicAlgCl p)).subtype).toIntLinearMap
          ((χ g.1) • (groupCohomology.Kummer.kummerRep ℚ_[p] (PadicAlgCl p) p).ρ g.1
            (Additive.ofMul (groupCohomology.Kummer.kummerCocycleRoots hα g.2))))
      ∈ groupCohomology.levelCoboundaries₂ (localGaloisToGlobal p)
          (Rep.ofAlgebraAutOnUnits ℚ_[p] (PadicAlgCl p)) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_smul_kummerCocycle_pairing_mem_levelCoboundaries2_of_thickening.solution
