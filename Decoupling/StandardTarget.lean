import Decoupling.ToricWindows
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The standard augmented free presentation

This is the actual direct sum of the three prefixes in Eq. (45) of
`notes/main.pdf`. The middle free summand occupies chain degree zero only:
it contributes check labels and contributes no physical qubits. The repeated
Koszul blocks use direction-first indices `(direction, copy)`, so their
ordering is `∂ⱼ ⊗ Iₜ`, with degree-two directions `(yz,zx,xy)`.

The augmentation is onto `𝔽₂^t₁ × (R^h × J^t₂)`. Exactness at degree zero
and at the physical module is proved from the actual Laurent Koszul complex,
including empty layers and an empty free summand.
-/

namespace Decoupling.StandardTarget

open Matrix PhysicalKoszul EvaluationLinear ToricWindows

noncomputable section

/-- Degree-zero check-label indices, including the middle free summand. -/
abbrev I₀ (t₁ h t₂ : ℕ) := Fin t₁ ⊕ (Fin h ⊕ (Fin 3 × Fin t₂))

/-- Physical qubits: three directions for each species, with no `h` block. -/
abbrev I₁ (t₁ t₂ : ℕ) := (Fin 3 × Fin t₁) ⊕ (Fin 3 × Fin t₂)

/-- Degree-two generators for the two toric species. -/
abbrev I₂ (t₁ t₂ : ℕ) := (Fin 3 × Fin t₁) ⊕ Fin t₂

abbrev G₀ (t₁ h t₂ : ℕ) := I₀ t₁ h t₂ → R
abbrev G₁ (t₁ t₂ : ℕ) := I₁ t₁ t₂ → R
abbrev G₂ (t₁ t₂ : ℕ) := I₂ t₁ t₂ → R

/-- The genuine standard syndrome module, with augmentation action on its first factor. -/
abbrev Nstd (t₁ h t₂ : ℕ) := Trivial t₁ × ((Fin h → R) × (Fin t₂ → J))

/-- Restriction to any chosen set of coordinates. -/
def coordinates {ι κ : Type*} (f : κ → ι) : (ι → R) →ₗ[R] (κ → R) :=
  LinearMap.pi fun k => LinearMap.proj (f k)

@[simp] theorem coordinates_apply {ι κ : Type*} (f : κ → ι) (v : ι → R) (k : κ) :
    coordinates f v k = v (f k) := rfl

/-- Coordinatewise evaluation, with the correct restricted scalar action on the target. -/
def evaluate (t : ℕ) : (Fin t → R) →ₗ[R] Trivial t where
  toFun a j := augmentation (a j)
  map_add' a b := by funext j; exact map_add augmentation (a j) (b j)
  map_smul' r a := by
    funext j
    exact map_mul augmentation r (a j)

@[simp] theorem evaluate_apply (t : ℕ) (a : Fin t → R) (j : Fin t) :
    evaluate t a j = augmentation (a j) := rfl

variable (t₁ h t₂ : ℕ)

/-- The first differential is `∂₁^(t₁) ⊕ 0 ⊕ ∂₂^(t₂)`. -/
def d₁ : G₁ t₁ t₂ →ₗ[R] G₀ t₁ h t₂ :=
  LinearMap.pi fun row => match row with
  | .inl j => (LinearMap.proj 0).comp
      (partial₁.mulVecLin.comp (coordinates fun i => .inl (i, j)))
  | .inr (.inl _) => 0
  | .inr (.inr (i, j)) => (LinearMap.proj i).comp
      (partial₂.mulVecLin.comp (coordinates fun k => .inr (k, j)))

/-- The next differential is `diag(∂₂^(t₁), ∂₃^(t₂))`. -/
def d₂ : G₂ t₁ t₂ →ₗ[R] G₁ t₁ t₂ :=
  LinearMap.pi fun row => match row with
  | .inl (i, j) => (LinearMap.proj i).comp
      (partial₂.mulVecLin.comp (coordinates fun k => .inl (k, j)))
  | .inr (i, j) => (LinearMap.proj i).comp
      (partial₃.mulVecLin.comp (coordinates fun (_ : Fin 1) => .inr j))

/-- The augmentation `(α,w) ↦ (α(1), b₁w)` of Eq. (47). -/
def ε : G₀ t₁ h t₂ →ₗ[R] Nstd t₁ h t₂ :=
  ((evaluate t₁).comp (coordinates Sum.inl)).prod
    ((coordinates fun j => Sum.inr (Sum.inl j)).prod
      (LinearMap.pi fun j => idealAugmentation.comp
        (coordinates fun i => Sum.inr (Sum.inr (i, j)))))

@[simp] theorem d₁_left (a : G₁ t₁ t₂) (j : Fin t₁) :
    d₁ t₁ h t₂ a (.inl j) = (partial₁ *ᵥ (fun i => a (.inl (i, j)))) 0 := rfl

@[simp] theorem d₁_free (a : G₁ t₁ t₂) (j : Fin h) :
    d₁ t₁ h t₂ a (.inr (.inl j)) = 0 := rfl

@[simp] theorem d₁_right (a : G₁ t₁ t₂) (i : Fin 3) (j : Fin t₂) :
    d₁ t₁ h t₂ a (.inr (.inr (i, j))) =
      (partial₂ *ᵥ (fun k => a (.inr (k, j)))) i := rfl

@[simp] theorem d₂_left (a : G₂ t₁ t₂) (i : Fin 3) (j : Fin t₁) :
    d₂ t₁ t₂ a (.inl (i, j)) = (partial₂ *ᵥ (fun k => a (.inl (k, j)))) i := rfl

@[simp] theorem d₂_right (a : G₂ t₁ t₂) (i : Fin 3) (j : Fin t₂) :
    d₂ t₁ t₂ a (.inr (i, j)) = (partial₃ *ᵥ (fun _ => a (.inr j))) i := rfl

@[simp] theorem ε_first (a : G₀ t₁ h t₂) (j : Fin t₁) :
    (ε t₁ h t₂ a).1 j = augmentation (a (.inl j)) := rfl

@[simp] theorem ε_free (a : G₀ t₁ h t₂) (j : Fin h) :
    (ε t₁ h t₂ a).2.1 j = a (.inr (.inl j)) := rfl

@[simp] theorem ε_ideal (a : G₀ t₁ h t₂) (j : Fin t₂) :
    (ε t₁ h t₂ a).2.2 j = idealAugmentation (fun i => a (.inr (.inr (i, j)))) := rfl

/-- The displayed standard augmentation is surjective. -/
theorem ε_surjective : Function.Surjective (ε t₁ h t₂) := by
  rintro ⟨a, b, c⟩
  choose v hv using fun j => idealAugmentation_surjective (c j)
  refine ⟨fun i => match i with
    | .inl j => constant (a j)
    | .inr (.inl j) => b j
    | .inr (.inr (k, j)) => v j k, ?_⟩
  apply Prod.ext
  · funext j
    exact augmentation_constant (a j)
  · apply Prod.ext
    · rfl
    · funext j
      exact hv j

/-- The standard chain condition at physical degree. -/
theorem d₁_comp_d₂ : (d₁ t₁ h t₂).comp (d₂ t₁ t₂) = 0 := by
  apply LinearMap.ext
  intro a
  funext row
  rcases row with j | j | ⟨i, j⟩
  · change (partial₁ *ᵥ (partial₂ *ᵥ (fun k => a (.inl (k, j))))) 0 = 0
    rw [mulVec_mulVec, partial₁_mul_partial₂, zero_mulVec]
    rfl
  · rfl
  · change (partial₂ *ᵥ (partial₃ *ᵥ (fun _ => a (.inr j)))) i = 0
    rw [mulVec_mulVec, partial₂_mul_partial₃, zero_mulVec]
    rfl

/-- Every augmentation-kernel vector is an actual standard boundary. -/
theorem exact_augmentation : LinearMap.range (d₁ t₁ h t₂) =
    LinearMap.ker (ε t₁ h t₂) := by
  apply Submodule.ext
  intro a
  change (∃ v, d₁ t₁ h t₂ v = a) ↔ ε t₁ h t₂ a = 0
  constructor
  · rintro ⟨v, rfl⟩
    apply Prod.ext
    · funext j
      change augmentation ((partial₁ *ᵥ (fun i => v (.inl (i, j)))) 0) = 0
      apply (PhysicalKoszul.exact_augmentation _).mpr
      refine ⟨fun i => v (.inl (i, j)), ?_⟩
      funext i
      fin_cases i
      rfl
    · apply Prod.ext
      · rfl
      · funext j
        change idealAugmentation (partial₂ *ᵥ (fun i => v (.inr (i, j)))) = 0
        apply LinearMap.mem_ker.mp
        rw [ker_idealAugmentation]
        exact ⟨fun i => v (.inr (i, j)), rfl⟩
  · intro ha
    have hfirst (j : Fin t₁) : augmentation (a (.inl j)) = 0 :=
      congrArg (fun z : Nstd t₁ h t₂ => z.1 j) ha
    have hfree (j : Fin h) : a (.inr (.inl j)) = 0 :=
      congrArg (fun z : Nstd t₁ h t₂ => z.2.1 j) ha
    have hlast (j : Fin t₂) :
        ∃ v, partial₂ *ᵥ v = (fun i => a (.inr (.inr (i, j)))) := by
      have hk : (fun i => a (.inr (.inr (i, j)))) ∈
          LinearMap.ker idealAugmentation :=
        congrArg (fun z : Nstd t₁ h t₂ => z.2.2 j) ha
      rw [ker_idealAugmentation] at hk
      exact hk
    choose v hv using fun j => (PhysicalKoszul.exact_augmentation _).mp (hfirst j)
    choose w hw using hlast
    refine ⟨Sum.elim (fun p => v p.2 p.1) (fun p => w p.2 p.1), ?_⟩
    funext row
    rcases row with j | j | ⟨i, j⟩
    · exact congrFun (hv j) 0
    · exact (hfree j).symm
    · exact congrFun (hw j) i

/-- The displayed `d₂` generates all physical cycles. -/
theorem exact_physical : LinearMap.range (d₂ t₁ t₂) =
    LinearMap.ker (d₁ t₁ h t₂) := by
  apply Submodule.ext
  intro a
  change (∃ v, d₂ t₁ t₂ v = a) ↔ d₁ t₁ h t₂ a = 0
  constructor
  · rintro ⟨v, rfl⟩
    exact DFunLike.congr_fun (d₁_comp_d₂ t₁ h t₂) v
  · intro ha
    have hleft (j : Fin t₁) : partial₁ *ᵥ (fun i => a (.inl (i, j))) = 0 := by
      funext i
      fin_cases i
      exact congrFun ha (.inl j)
    have hright (j : Fin t₂) : partial₂ *ᵥ (fun i => a (.inr (i, j))) = 0 := by
      funext i
      exact congrFun ha (.inr (.inr (i, j)))
    choose v hv using fun j => (exact_partial₁_partial₂ _).mp (hleft j)
    choose w hw using fun j => (exact_partial₂_partial₃ _).mp (hright j)
    refine ⟨Sum.elim (fun p => v p.2 p.1) (fun j => w j 0), ?_⟩
    funext row
    rcases row with ⟨i, j⟩ | ⟨i, j⟩
    · exact congrFun (hv j) i
    · have hwj : (fun _ : Fin 1 => w j 0) = w j := by
        funext k
        fin_cases k
        rfl
      change (partial₃ *ᵥ (fun _ => w j 0)) i = _
      rw [hwj]
      exact congrFun (hw j) i

/-- The first differential as the actual manuscript matrix. -/
def D₁ : Matrix (I₀ t₁ h t₂) (I₁ t₁ t₂) R := LinearMap.toMatrix' (d₁ t₁ h t₂)

/-- The physical boundary matrix as the actual manuscript matrix. -/
def D₂ : Matrix (I₁ t₁ t₂) (I₂ t₁ t₂) R := LinearMap.toMatrix' (d₂ t₁ t₂)

@[simp] theorem D₁_mulVec (a : G₁ t₁ t₂) : D₁ t₁ h t₂ *ᵥ a = d₁ t₁ h t₂ a :=
  LinearMap.toMatrix'_mulVec _ _

@[simp] theorem D₂_mulVec (a : G₂ t₁ t₂) : D₂ t₁ t₂ *ᵥ a = d₂ t₁ t₂ a :=
  LinearMap.toMatrix'_mulVec _ _

/-- The first repeated block is precisely `∂₁ ⊗ Iₜ₁`. -/
theorem D₁_first_block (j k : Fin t₁) (i : Fin 3) :
    D₁ t₁ h t₂ (.inl j) (.inl (i, k)) = if j = k then partial₁ 0 i else 0 := by
  by_cases hj : j = k
  · subst k
    fin_cases i <;> simp [D₁, LinearMap.toMatrix'_apply, d₁_left,
      Matrix.mulVec, dotProduct, Koszul.d₁, Pi.single_apply]
  · fin_cases i <;> simp [D₁, LinearMap.toMatrix'_apply, d₁_left,
      Matrix.mulVec, dotProduct, Koszul.d₁, hj]

/-- The degree-zero free block has identically zero incoming differential. -/
@[simp] theorem D₁_free_row (j : Fin h) (col : I₁ t₁ t₂) :
    D₁ t₁ h t₂ (.inr (.inl j)) col = 0 := rfl

/-- The third repeated block is precisely `∂₂ ⊗ Iₜ₂`. -/
theorem D₁_second_block (i k : Fin 3) (j l : Fin t₂) :
    D₁ t₁ h t₂ (.inr (.inr (i, j))) (.inr (k, l)) =
      if j = l then partial₂ i k else 0 := by
  by_cases hj : j = l
  · subst l
    fin_cases i <;> fin_cases k <;> simp [D₁, LinearMap.toMatrix'_apply, d₁_right,
      Matrix.mulVec, dotProduct, Koszul.d₂, Pi.single_apply]
  · fin_cases i <;> fin_cases k <;> simp [D₁, LinearMap.toMatrix'_apply, d₁_right,
      Matrix.mulVec, dotProduct, Koszul.d₂, hj]

@[simp] theorem D₁_first_cross (j : Fin t₁) (i : Fin 3) (k : Fin t₂) :
    D₁ t₁ h t₂ (.inl j) (.inr (i, k)) = 0 := by
  simp [D₁, LinearMap.toMatrix'_apply, d₁_left, Matrix.mulVec, dotProduct]

@[simp] theorem D₁_second_cross (i k : Fin 3) (j : Fin t₂) (l : Fin t₁) :
    D₁ t₁ h t₂ (.inr (.inr (i, j))) (.inl (k, l)) = 0 := by
  simp [D₁, LinearMap.toMatrix'_apply, d₁_right, Matrix.mulVec, dotProduct]

/-- The physical first-species boundary block is precisely `∂₂ ⊗ Iₜ₁`. -/
theorem D₂_first_block (i k : Fin 3) (j l : Fin t₁) :
    D₂ t₁ t₂ (.inl (i, j)) (.inl (k, l)) =
      if j = l then partial₂ i k else 0 := by
  by_cases hj : j = l
  · subst l
    fin_cases i <;> fin_cases k <;> simp [D₂, LinearMap.toMatrix'_apply, d₂_left,
      Matrix.mulVec, dotProduct, Koszul.d₂, Pi.single_apply]
  · fin_cases i <;> fin_cases k <;> simp [D₂, LinearMap.toMatrix'_apply, d₂_left,
      Matrix.mulVec, dotProduct, Koszul.d₂, hj]

/-- The physical second-species boundary block is precisely `∂₃ ⊗ Iₜ₂`. -/
theorem D₂_second_block (i : Fin 3) (j l : Fin t₂) :
    D₂ t₁ t₂ (.inr (i, j)) (.inr l) = if j = l then partial₃ i 0 else 0 := by
  by_cases hj : j = l
  · subst l
    fin_cases i <;> simp [D₂, LinearMap.toMatrix'_apply, d₂_right,
      Matrix.mulVec, dotProduct, Koszul.d₃]
  · fin_cases i <;> simp [D₂, LinearMap.toMatrix'_apply, d₂_right,
      Matrix.mulVec, dotProduct, Koszul.d₃, hj]

@[simp] theorem D₂_first_cross (i : Fin 3) (j : Fin t₁) (k : Fin t₂) :
    D₂ t₁ t₂ (.inl (i, j)) (.inr k) = 0 := by
  simp [D₂, LinearMap.toMatrix'_apply, d₂_left, Matrix.mulVec, dotProduct]

@[simp] theorem D₂_second_cross (i k : Fin 3) (j : Fin t₂) (l : Fin t₁) :
    D₂ t₁ t₂ (.inr (i, j)) (.inl (k, l)) = 0 := by
  simp [D₂, LinearMap.toMatrix'_apply, d₂_right, Matrix.mulVec, dotProduct]

theorem D₁_mul_D₂ : D₁ t₁ h t₂ * D₂ t₁ t₂ = 0 := by
  apply Matrix.toLin'.injective
  simpa only [D₁, D₂, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero]
    using d₁_comp_d₂ t₁ h t₂

theorem exact_augmentation_matrix : LinearMap.range (D₁ t₁ h t₂).mulVecLin =
    LinearMap.ker (ε t₁ h t₂) := by
  have hD : (D₁ t₁ h t₂).mulVecLin = d₁ t₁ h t₂ := by
    apply LinearMap.ext
    intro a
    exact D₁_mulVec _ _ _ a
  rw [hD]
  exact exact_augmentation t₁ h t₂

theorem exact_physical_matrix : LinearMap.range (D₂ t₁ t₂).mulVecLin =
    LinearMap.ker (D₁ t₁ h t₂).mulVecLin := by
  have hD₁ : (D₁ t₁ h t₂).mulVecLin = d₁ t₁ h t₂ := by
    apply LinearMap.ext
    intro a
    exact D₁_mulVec _ _ _ a
  have hD₂ : (D₂ t₁ t₂).mulVecLin = d₂ t₁ t₂ := by
    apply LinearMap.ext
    intro a
    exact D₂_mulVec _ _ a
  rw [hD₁, hD₂]
  exact exact_physical t₁ h t₂

/-- The actual cokernel of the standard presentation is the advertised syndrome module. -/
def cokernelEquiv :
    (G₀ t₁ h t₂ ⧸ LinearMap.range (d₁ t₁ h t₂)) ≃ₗ[R] Nstd t₁ h t₂ :=
  (Submodule.quotEquivOfEq _ _ (exact_augmentation t₁ h t₂)).trans
    ((ε t₁ h t₂).quotKerEquivOfSurjective (ε_surjective t₁ h t₂))

@[simp] theorem cokernelEquiv_mk (a : G₀ t₁ h t₂) :
    cokernelEquiv t₁ h t₂ (Submodule.Quotient.mk a) = ε t₁ h t₂ a := rfl

theorem card_I₀ : Fintype.card (I₀ t₁ h t₂) = t₁ + h + 3 * t₂ := by
  simp [I₀, Nat.add_assoc]

theorem card_I₁ : Fintype.card (I₁ t₁ t₂) = 3 * t₁ + 3 * t₂ := by simp [I₁]

theorem card_I₂ : Fintype.card (I₂ t₁ t₂) = 3 * t₁ + t₂ := by simp [I₂]

end

end Decoupling.StandardTarget
