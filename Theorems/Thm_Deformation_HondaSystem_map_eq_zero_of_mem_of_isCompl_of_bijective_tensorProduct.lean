import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct

open scoped TensorProduct

universe u v

theorem Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (v : ℕ)
    (Gc Ge : Type v) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc]
    [Module.Finite (ZMod p) Gc] [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge]
    [Module.Finite (ZMod p) Ge]
    (qc : G v →ₐc[ZMod p] Gc) (πe : G v →ₐc[ZMod p] Ge) (Θ : G v →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hΘ : Function.Bijective Θ)
    (hΘapply : ∀ b, Θ b = Algebra.TensorProduct.map (qc : G v →ₐ[ZMod p] Gc) (πe : G v →ₐ[ZMod p] Ge)
      (Coalgebra.comul (R := ZMod p) b))
    (hGc : IsLocalRing Gc) (hGe : IsReduced Ge)
    (Mc Met : Submodule 𝓞 (Fin r → 𝓞))
    (hMet : ∀ m, m ∈ Met ↔ ∀ N : ℕ, ∃ y, (H₁.F ^ N) y = m)
    (hMc : ∀ m, m ∈ Mc ↔ ∀ k : ℕ, ∃ N : ℕ, ∃ y, (H₁.F ^ N) m = (p : 𝓞) ^ k • y) :
    (∀ m ∈ Mc, Deformation.DieudonneModule.map (ZMod p) p πe (π v m) = 0) ∧
    (∀ m ∈ Met, Deformation.DieudonneModule.map (ZMod p) p qc (π v m) = 0) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct.solution
