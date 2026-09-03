import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback
    {A₀ : Type u} [CommRing A₀] {n : ℕ} {Z₀ : Scheme.{u}}
    (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀)) [IsClosedImmersion ι₀]
    (K : Type u) [Field K] [Algebra A₀ K] {ZK : Scheme.{u}}
    (ιK : ZK ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) [IsClosedImmersion ιK]
    (e : ZK ⟶ Z₀)
    (hpb : IsPullback e (ιK ≫ ProjSpace.π K n) (ι₀ ≫ ProjSpace.π A₀ n) (Spec.map (CommRingCat.ofHom (algebraMap A₀ K))))
    (hcomp : e ≫ ι₀ = ιK ≫ ProjSpace.map A₀ K n) (d : ℕ)
    (Θ₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d) →ₗ[A₀] (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).cochain (ProjSpace.stdCoverPullback ι₀) 0)
    (hΘ₀ : ∀ (F : MvPolynomial (Fin (n + 1)) A₀) (hF : F.IsHomogeneous d) (s : (ProjSpace.stdCoverPullback ι₀).Idx 0) (i : Fin (n + 1)),
      (Θ₀ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ s).val i =
        ProjSpace.restrictFun
          (inf_le_right : (ProjSpace.stdCoverPullback ι₀).inter s ⊓ ProjSpace.pullbackChart ι₀ i ≤ ProjSpace.pullbackChart ι₀ i)
          ((ι₀.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))))
    (h : ℕ → ℕ) (q : Point K n h)
    (hq : ∀ (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d),
      (F ∈ q.I ↔ ∀ i : Fin (n + 1), ((ιK.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))) = 0))
    (ha : ∀ i : ℕ, Subsingleton ((ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).HSucc (ProjSpace.stdCoverPullback ιK) i))
    (hb : ∀ c ∈ (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).H0 (ProjSpace.stdCoverPullback ιK),
      ∃ (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d),
        ∀ (s : (ProjSpace.stdCoverPullback ιK).Idx 0) (i : Fin (n + 1)),
          (c s).val i =
            ProjSpace.restrictFun
              (inf_le_right : (ProjSpace.stdCoverPullback ιK).inter s ⊓ ProjSpace.pullbackChart ιK i ≤ ProjSpace.pullbackChart ιK i)
              ((ιK.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })))) :
    (∀ i : ℕ, LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) (i + 1)).baseChange K) ≤
      LinearMap.range (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) i).baseChange K)) ∧
    LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange K) ≤ LinearMap.range (Θ₀.baseChange K) ∧
    Module.finrank K (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange K)) = h d := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.solution
