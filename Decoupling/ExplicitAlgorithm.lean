import Decoupling.DecouplingFromSplitting
import Decoupling.CoarseVanishing

/-!
# The literal representative matrices used by the algorithm

This file connects Appendix C's cycle representatives and corrected lift to
the selected degree-zero comparison map `φ₀=(T V′)`.  The comparison equations
are constructed while preserving that exact matrix, rather than replacing it
by an unspecified lift of the same augmentation isomorphism.
-/

namespace Decoupling.ExplicitAlgorithm

open Matrix EvaluationLinear ExplicitSplitting StandardTarget

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512

variable {q s k t₁ t₂ : ℕ}
variable (c : Syndrome.Cochain R (Fin q → R) (Fin s → R) (Fin k → R))
variable (e₁ : Trivial t₁ ≃ₗ[R] c.C1) (e₂ : c.C2 ≃ₗ[R] Trivial t₂)

/-- The columns of `V`, with the free labels first and direction-first toric
labels second.  These are all check labels, not extra physical qubits. -/
abbrev WIndex (h t : ℕ) := Fin h ⊕ (Fin 3 × Fin t)

/-- The displayed `diag(I_h,∂₁^(t))`, with its codomain the actual ideal. -/
def residualAugmentation (h t : ℕ) :
    (WIndex h t → R) →ₗ[R] ((Fin h → R) × (Fin t → J)) :=
  (coordinates Sum.inl).prod (LinearMap.pi fun j =>
    ToricWindows.idealAugmentation.comp (coordinates fun i => Sum.inr (i, j)))

/-- `b₁` interpreted in the original actual image module through the proved
normalization, so no normalized cover is assumed as input. -/
def b₁ : (WIndex (k - t₂) t₂ → R) →ₗ[R] c.L :=
  (imageNormalization c e₂).symm.toLinearMap.comp (residualAugmentation (k - t₂) t₂)

/-- The relation matrix `(0,∂₂^(t))ᵀ` of III.C. -/
def b₂ (h t : ℕ) : Matrix (WIndex h t) (Fin 3 × Fin t) R :=
  Matrix.fromRows 0 (fun i j => if i.2 = j.2 then PhysicalKoszul.partial₂ i.1 j.1 else 0)

theorem b₂_mulVec (h t : ℕ) (v : (Fin 3 × Fin t) → R) :
    b₂ h t *ᵥ v = Sum.elim (0 : Fin h → R)
      (fun i => (PhysicalKoszul.partial₂ *ᵥ fun j => v (j, i.2)) i.1) := by
  funext row
  rcases row with i | i
  · simp [b₂, Matrix.mulVec, dotProduct]
  · simp [b₂, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-- The entire residual presentation has the stated kernel, not merely d²=0. -/
theorem exact_residualAugmentation (h t : ℕ) :
    LinearMap.range (b₂ h t).mulVecLin = LinearMap.ker (residualAugmentation h t) := by
  apply Submodule.ext
  intro v
  constructor
  · rintro ⟨w, rfl⟩
    change residualAugmentation h t (b₂ h t *ᵥ w) = 0
    rw [b₂_mulVec]
    apply Prod.ext
    · rfl
    · funext j
      change ToricWindows.idealAugmentation
        (PhysicalKoszul.partial₂ *ᵥ fun i => w (i, j)) = 0
      apply LinearMap.mem_ker.mp
      rw [ToricWindows.ker_idealAugmentation]
      exact ⟨fun i => w (i, j), rfl⟩
  · intro hv
    have hfree (j : Fin h) : v (.inl j) = 0 := congrArg (fun x => x.1 j) hv
    have hbound (j : Fin t) :
        (fun i => v (.inr (i, j))) ∈ LinearMap.range PhysicalKoszul.partial₂.mulVecLin := by
      rw [← ToricWindows.ker_idealAugmentation]
      exact congrArg (fun x => x.2 j) hv
    choose w hw using hbound
    refine ⟨fun p => w p.2 p.1, ?_⟩
    change b₂ h t *ᵥ (fun p => w p.2 p.1) = v
    rw [b₂_mulVec]
    funext row
    rcases row with j | ⟨i, j⟩
    · exact (hfree j).symm
    · exact congrFun (hw j) i

theorem exact_b₂_b₁ : LinearMap.range (b₂ (k - t₂) t₂).mulVecLin =
    LinearMap.ker (b₁ c e₂) := by
  rw [exact_residualAugmentation]
  apply Submodule.ext
  intro v
  change residualAugmentation (k - t₂) t₂ v = 0 ↔
    (imageNormalization c e₂).symm (residualAugmentation (k - t₂) t₂ v) = 0
  exact ⟨fun hv => hv ▸ map_zero _, fun hv =>
    (imageNormalization c e₂).symm.injective (hv.trans (map_zero _).symm)⟩

def partial₁Copies (t : ℕ) : Matrix (Fin t) (Fin 3 × Fin t) R :=
  fun j i => if j = i.2 then PhysicalKoszul.partial₁ 0 i.1 else 0

/-- The three printed row blocks are exactly the two-block presentation used
to split the two forward solves. -/
theorem D₁_blocks (t₁ h t₂ : ℕ) : D₁ t₁ h t₂ =
    Matrix.fromBlocks (partial₁Copies t₁) 0 0 (b₂ h t₂) := by
  apply Matrix.ext
  intro row col
  rcases row with i | i | ⟨i, j⟩ <;> rcases col with ⟨l, m⟩ | ⟨l, m⟩
  · exact D₁_first_block _ _ _ _ _ _
  · exact D₁_first_cross _ _ _ _ _ _
  · exact D₁_free_row _ _ _ _ _
  · exact D₁_free_row _ _ _ _ _
  · exact D₁_second_cross _ _ _ _ _ _ _
  · exact D₁_second_block _ _ _ _ _ _ _

/-- The correction formula with the manuscript's actual finite column index. -/
def corrected {ι : Type} [Fintype ι] (T : Matrix (Fin s) (Fin t₁) R)
    (C : Matrix (Fin t₁) (Fin s) (ZMod 2)) (V : Matrix (Fin s) ι R) :
    Matrix (Fin s) ι R := V + T * (C * V.map augmentation).map constant

section Correction

variable (r : RetractionData R (Trivial t₁) c.N c.L)
variable {ι : Type} [Fintype ι]
variable (T : Matrix (Fin s) (Fin t₁) R) (V : Matrix (Fin s) ι R)
variable (hT : ∀ a : Fin t₁ → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a))

include hT in
theorem corrected_class (w : ι → R) :
    c.ε (corrected T (retractionMatrix c r) V *ᵥ w) =
      r.correction (c.ε (V *ᵥ w)) := by
  have heval (D : Matrix (Fin t₁) ι (ZMod 2)) :
      augmentation ∘ (D.map constant *ᵥ w) = D *ᵥ (augmentation ∘ w) := by
    have hD : (D.map constant).map augmentation = D := by
      apply Matrix.ext
      intro i j
      simp
    funext i
    exact (augmentation.map_mulVec (D.map constant) w i).trans (by rw [hD])
  have hV : V.map augmentation *ᵥ (augmentation ∘ w) =
      augmentation ∘ (V *ᵥ w) := by
    funext i
    exact (augmentation.map_mulVec V w i).symm
  rw [corrected, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, map_add, hT, heval,
    ← Matrix.mulVec_mulVec, hV]
  change c.ε (V *ᵥ w) + r.ι (evalMatrix (retractionMatrix c r) (V *ᵥ w)) = _
  rw [retractionMatrix_eval]
  rfl

include hT in
theorem corrected_descends (hπ : r.π = c.π) (b : (ι → R) →ₗ[R] c.L)
    (hV : ∀ w, c.π (c.ε (V *ᵥ w)) = b w) (w : ι → R) :
    c.ε (corrected T (retractionMatrix c r) V *ᵥ w) = r.σ (b w) := by
  rw [corrected_class c r T V hT]
  have hw : r.π (c.ε (V *ᵥ w)) = b w := by rw [hπ]; exact hV w
  rw [← hw, r.σ_π]

end Correction

/-- The data are actual cycle representatives, a retraction, and lifts of b₁.
They are constructed below from κ=0, rather than requested as extra inputs. -/
structure Data where
  p : c.N →ₗ[R] Trivial t₁
  retract : p.comp (c.ι.comp e₁.toLinearMap) = LinearMap.id
  T : Matrix (Fin s) (Fin t₁) R
  V : Matrix (Fin s) (WIndex (k - t₂) t₂) R
  T_class : ∀ a : Fin t₁ → R, c.ε (T *ᵥ a) = c.ι (e₁ (augmentation ∘ a))
  V_projection : ∀ w, c.π (c.ε (V *ᵥ w)) = b₁ c e₂ w

namespace Data

variable {c e₁ e₂} (a : Data c e₁ e₂)

def retraction : RetractionData R (Trivial t₁) c.N c.L :=
  ofSyndrome c e₁ a.p a.retract

def C : Matrix (Fin t₁) (Fin s) (ZMod 2) := retractionMatrix c a.retraction
def Vprime : Matrix (Fin s) (WIndex (k - t₂) t₂) R := corrected a.T a.C a.V
def φ₀ : Matrix (Fin s) (I₀ t₁ (k - t₂) t₂) R := Matrix.fromCols a.T a.Vprime
def β : Nstd t₁ (k - t₂) t₂ ≃ₗ[R] c.N := augmentationIso c e₁ e₂ a.p a.retract

/-- The selected representatives satisfy the manuscript's cycle equation. -/
theorem γ_T : c.γ.comp a.T.mulVecLin = 0 := by
  apply LinearMap.ext
  intro v
  have hv := congrArg c.π (a.T_class v)
  have hz : c.π (c.ι (e₁ (augmentation ∘ v))) = 0 :=
    DFunLike.congr_fun c.π_ι _
  exact (congrArg Subtype.val hv).trans (congrArg Subtype.val hz)

/-- The boundary criterion for all Laurent coefficients, including zero rank. -/
theorem T_boundary_iff (v : Fin t₁ → R) :
    a.T *ᵥ v ∈ LinearMap.range c.d₁ ↔ augmentation ∘ v = 0 := by
  rw [← Submodule.Quotient.mk_eq_zero]
  change c.ε (a.T *ᵥ v) = 0 ↔ augmentation ∘ v = 0
  rw [a.T_class]
  constructor
  · intro hv
    exact e₁.injective (c.ι_injective (hv.trans (map_zero c.ι).symm) |>.trans
      (map_zero e₁).symm)
  · intro hv
    rw [hv, map_zero, map_zero]

/-- Both original finite-field equations are consequences of the retraction. -/
theorem C_equations :
    a.C * atOne (LinearMap.toMatrix' c.d₁) = 0 ∧ a.C * atOne a.T = 1 :=
  ⟨retractionMatrix_boundary c a.retraction,
    retractionMatrix_T c a.retraction a.T a.T_class⟩

/-- The representative formula is literally the matrix used in C.1. -/
theorem Vprime_formula : a.Vprime = a.V + a.T * (a.C * a.V.map augmentation).map constant := rfl

theorem Vprime_descends (w : WIndex (k - t₂) t₂ → R) :
    c.ε (a.Vprime *ᵥ w) = a.retraction.σ (b₁ c e₂ w) :=
  corrected_descends c a.retraction a.T a.V a.T_class rfl (b₁ c e₂) a.V_projection w

/-- Every column of the exact literal product `V′b₂` is a boundary. -/
theorem Vprime_b₂_boundaries :
    LinearMap.range (a.Vprime * b₂ (k - t₂) t₂).mulVecLin ≤ LinearMap.range c.d₁ := by
  rintro _ ⟨w, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change c.ε ((a.Vprime * b₂ (k - t₂) t₂) *ᵥ w) = 0
  rw [← Matrix.mulVec_mulVec, a.Vprime_descends]
  have hw : b₁ c e₂ (b₂ (k - t₂) t₂ *ᵥ w) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [← exact_b₂_b₁]
    exact ⟨w, rfl⟩
  rw [hw, map_zero]

/-- The precise block `(T V′)` lifts the constructed normalized β. -/
theorem augmentation_square : c.ε.comp a.φ₀.mulVecLin =
    a.β.toLinearMap.comp (StandardTarget.ε t₁ (k - t₂) t₂) := by
  apply LinearMap.ext
  intro v
  change c.ε ((Matrix.fromCols a.T a.Vprime) *ᵥ v) = _
  rw [Matrix.fromCols_mulVec, map_add, a.T_class, a.Vprime_descends]
  rfl

end Data

/-- κ=0 constructs the exact representative matrices of Appendix C. -/
theorem exists_data (hκ : c.κ = 0) : Nonempty (Data c e₁ e₂) := by
  obtain ⟨p, hp⟩ := SplitAssembly.exists_retraction_of_κ_zero c hκ e₁
  let r := ofSyndrome c e₁ p hp
  obtain ⟨T, hT⟩ := exists_T c r
  obtain ⟨V, hV⟩ := Module.projective_lifting_property c.γ.rangeRestrict (b₁ c e₂)
    c.γ.surjective_rangeRestrict
  refine ⟨⟨p, hp, T, LinearMap.toMatrix' V, hT, ?_⟩⟩
  intro w
  rw [LinearMap.toMatrix'_mulVec, c.π_mk]
  exact DFunLike.congr_fun hV w

/-- The algorithm's chosen degree-zero matrix is retained by all comparison
solves.  Both homotopies and the reverse augmentation are actual conclusions. -/
theorem exists_comparison_of_data (a : Data c e₁ e₂) :
    ∃ d : Stabilization.ComparisonData R (Fin s) (Fin q)
      (I₀ t₁ (k - t₂) t₂) (I₁ t₁ t₂),
      d.d₁ = LinearMap.toMatrix' c.d₁ ∧ d.td₁ = D₁ t₁ (k - t₂) t₂ ∧
      d.φ₀ = a.φ₀ ∧
      c.ε.comp d.φ₀.mulVecLin = a.β.toLinearMap.comp (StandardTarget.ε t₁ (k - t₂) t₂) ∧
      (StandardTarget.ε t₁ (k - t₂) t₂).comp d.ρ₀.mulVecLin = a.β.symm.toLinearMap.comp c.ε := by
  have hF : LinearMap.range (LinearMap.toMatrix' c.d₁).mulVecLin = LinearMap.ker c.ε := by
    change LinearMap.range (Matrix.toLin' (LinearMap.toMatrix' c.d₁)) = _
    rw [Matrix.toLin'_toMatrix']
    exact (LinearMap.range c.d₁).ker_mkQ.symm
  obtain ⟨d, hd, htd, hφ, hε, hρ⟩ := Comparison.exists_comparisonData_of_lift
    (LinearMap.toMatrix' c.d₁) (D₁ t₁ (k - t₂) t₂) c.ε
    (StandardTarget.ε t₁ (k - t₂) t₂) (ε_surjective _ _ _) hF
    (exact_augmentation_matrix _ _ _) a.β a.φ₀.mulVecLin a.augmentation_square
  refine ⟨d, hd, htd, ?_, hε, hρ⟩
  change d.φ₀ = LinearMap.toMatrix' (Matrix.toLin' a.φ₀) at hφ
  simpa only [LinearMap.toMatrix'_toLin'] using hφ

/-- No representative data, retraction, β or comparison are assumed here. -/
theorem exists_explicit_comparison (hκ : c.κ = 0) :
    ∃ a : Data c e₁ e₂, ∃ d : Stabilization.ComparisonData R (Fin s) (Fin q)
      (I₀ t₁ (k - t₂) t₂) (I₁ t₁ t₂),
      d.d₁ = LinearMap.toMatrix' c.d₁ ∧ d.td₁ = D₁ t₁ (k - t₂) t₂ ∧
      d.φ₀ = Matrix.fromCols a.T (a.V + a.T * (a.C * a.V.map augmentation).map constant) ∧
      c.ε.comp d.φ₀.mulVecLin = a.β.toLinearMap.comp (StandardTarget.ε t₁ (k - t₂) t₂) := by
  obtain ⟨a⟩ := exists_data c e₁ e₂ hκ
  obtain ⟨d, hd, htd, hφ, hε, _⟩ := exists_comparison_of_data c e₁ e₂ a
  exact ⟨a, d, hd, htd, hφ, hε⟩

namespace Data

variable {c e₁ e₂} (a : Data c e₁ e₂)

/-- The produced comparison solves the two separate equations printed in
III.3, with `X₁,Y` precisely the two column blocks of its actual `φ₁`. -/
theorem forward_solves
    (d : Stabilization.ComparisonData R (Fin s) (Fin q)
      (I₀ t₁ (k - t₂) t₂) (I₁ t₁ t₂))
    (hd : d.d₁ = LinearMap.toMatrix' c.d₁) (htd : d.td₁ = D₁ t₁ (k - t₂) t₂)
    (hφ : d.φ₀ = a.φ₀) :
    LinearMap.toMatrix' c.d₁ * d.φ₁.submatrix id Sum.inl = a.T * partial₁Copies t₁ ∧
      LinearMap.toMatrix' c.d₁ * d.φ₁.submatrix id Sum.inr = a.Vprime * b₂ (k - t₂) t₂ := by
  have hforward := d.forward
  rw [hd, htd, hφ, φ₀, D₁_blocks, Matrix.fromCols_mul_fromBlocks] at hforward
  simp only [Matrix.mul_zero, add_zero, zero_add] at hforward
  constructor
  · apply Matrix.ext
    intro i j
    exact congrFun (congrFun hforward i) (.inl j)
  · apply Matrix.ext
    intro i j
    exact congrFun (congrFun hforward i) (.inr j)

end Data

section CircuitCertificate

open DecouplingFromSplitting PhysicalIsomorphism

variable {r cX : ℕ} {checks : CSS.Checks q s r}
variable (resolution : ResolutionExt.CSSResolution checks cX)
variable (layer₁ : Trivial t₁ ≃ₗ[R] resolution.cochain.C1)
variable (layer₂ : resolution.cochain.C2 ≃ₗ[R] Trivial t₂)

/-- The complete physical certificate is constructed with the literal
algorithm matrix as its selected `φ₀`, and the same constructed β. -/
theorem exists_explicit_certificate (hTop : checks.Topological) (hκ : resolution.cochain.κ = 0) :
    ∃ a : Data resolution.cochain layer₁ layer₂,
      ∃ out : Certificate checks cX t₁ t₂,
        out.comparison.φ₀ = a.φ₀ ∧ out.β = a.β := by
  obtain ⟨a⟩ := exists_data resolution.cochain layer₁ layer₂ hκ
  obtain ⟨d, hdF, hdG, hφ, hε, _⟩ :=
    exists_comparison_of_data resolution.cochain layer₁ layer₂ a
  change d.d₁ = LinearMap.toMatrix' (Matrix.toLin' checks.H_X) at hdF
  rw [LinearMap.toMatrix'_toLin'] at hdF
  have hF : ∀ v, d.d₁ *ᵥ v = 0 ↔ ∃ z, dagger checks.H_Z *ᵥ z = v := by
    intro v
    rw [hdF]
    exact checks.exact_X hTop v
  have hG : ∀ v, d.td₁ *ᵥ v = 0 ↔ ∃ z, D₂ t₁ t₂ *ᵥ z = v := by
    intro v
    rw [hdG]
    change v ∈ LinearMap.ker (D₁ t₁ (cX - t₂) t₂).mulVecLin ↔
      v ∈ LinearMap.range (D₂ t₁ t₂).mulVecLin
    rw [exact_physical_matrix]
  obtain ⟨hinv, hz, hx⟩ := stable_physical_isomorphism d
    (dagger checks.H_Z) (D₂ t₁ t₂) hF hG
  obtain ⟨word, hwz, hwx, depth, range, hd, hr⟩ := Circuit.block_circuit
    d.L₁ d.M₁ (speciesOrder q s cX t₁ t₂)
  refine ⟨a, {
    layer₂_le_cover := second_layer_rank_le resolution.cochain layer₂
    β := a.β
    comparison := d
    input_d₁ := hdF
    target_d₁ := hdG
    augmentation_square := hε
    inverse := hinv
    physical_square := d.physical_square
    z_image := hz
    x_image := hx
    circuit := word
    circuit_z := hwz
    circuit_x := hwx
    depth := depth
    range := range
    depth_eq := hd
    range_le := hr
  }, hφ, rfl⟩

end CircuitCertificate

section RepeatedComparison

open RetainedRing CoarseVanishing MatrixCopies

def a₃R (t : ℕ) : K₀ R t →ₗ[R] K₁ R t := across t PhysicalKoszul.partial₃.mulVecLin
def a₃S (t : ℕ) : K₀ S t →ₗ[S] K₁ S t := across t RetainedKoszul.d₃.mulVecLin
def χ₃ (t : ℕ) : K₀ S t →ₗ[S] K₀ R t := across t (Koszul.χ₃Over S u v w)

/-- The omitted repeated degree-three equation, in the same direction-first
ordering as the already proved degree-one and degree-two equations. -/
theorem comparison₃ (t : ℕ) : ((a₃R t).restrictScalars S).comp (χ₃ t) =
    (CoarseVanishing.χ₂ t).comp (a₃S t) := by
  apply LinearMap.ext
  intro a
  funext p
  exact congrFun (RetainedRing.comparison₃ (fun i => a (i, p.2))) p.1

theorem exact_a₃S_a₂S (t : ℕ) : LinearMap.range (a₃S t) = LinearMap.ker (a₂S t) := by
  apply exact_across
  apply Submodule.ext
  intro a
  exact (RetainedKoszul.exact_d₂_d₃ a).symm

end RepeatedComparison

end
end Decoupling.ExplicitAlgorithm
