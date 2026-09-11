import LeanCfgProject.SCLCompression.CompletelyRegularKernel

namespace LeanCfgProject
namespace SCLCompression

universe u v w

/--
Normalized Rees-matrix data for one completely simple component
`M[G; I, Lambda; Q]` from Section 8 of the manuscript.
-/
structure ReesData (I : Type u) (Lambda : Type v) (G : Type w) [Group G] where
  sandwich : Lambda → I → G
  row0 : I
  col0 : Lambda
  row_normalized : ∀ i : I, sandwich col0 i = 1
  col_normalized : ∀ l : Lambda, sandwich l row0 = 1

/-- An element `(i,g,lambda)` of a Rees matrix semigroup. -/
structure ReesMatrix
    {I : Type u} {Lambda : Type v} {G : Type w} [Group G]
    (D : ReesData I Lambda G) where
  row : I
  group : G
  col : Lambda

namespace ReesMatrix

variable {I : Type u} {Lambda : Type v} {G : Type w} [Group G]
variable (D : ReesData I Lambda G)

@[ext] theorem rees_ext {x y : ReesMatrix D}
    (hrow : x.row = y.row)
    (hgroup : x.group = y.group)
    (hcol : x.col = y.col) : x = y := by
  cases x
  cases y
  simp_all

/-- The normalized Rees multiplication `(i,g,l)(j,h,m)=(i,g q_{lj} h,m)`. -/
def mul (x y : ReesMatrix D) : ReesMatrix D :=
  ⟨x.row, x.group * D.sandwich x.col y.row * y.group, y.col⟩

instance : Mul (ReesMatrix D) := ⟨mul D⟩

@[simp] theorem mul_row (x y : ReesMatrix D) : (x * y).row = x.row := rfl
@[simp] theorem mul_group (x y : ReesMatrix D) :
    (x * y).group = x.group * D.sandwich x.col y.row * y.group := rfl
@[simp] theorem mul_col (x y : ReesMatrix D) : (x * y).col = y.col := rfl

instance : Semigroup (ReesMatrix D) where
  mul_assoc := by
    intro x y z
    ext <;> simp [mul_assoc]

/-- Distinguished normalized idempotent `e=(1,1,1)`. -/
def e : ReesMatrix D := ⟨D.row0, 1, D.col0⟩

/-- The distinguished maximal subgroup copy `bar g=(1,g,1)`. -/
def bar (g : G) : ReesMatrix D := ⟨D.row0, g, D.col0⟩

@[simp] theorem e_row : (e D).row = D.row0 := rfl
@[simp] theorem e_group : (e D).group = 1 := rfl
@[simp] theorem e_col : (e D).col = D.col0 := rfl
@[simp] theorem bar_row (g : G) : (bar D g).row = D.row0 := rfl
@[simp] theorem bar_group (g : G) : (bar D g).group = g := rfl
@[simp] theorem bar_col (g : G) : (bar D g).col = D.col0 := rfl

@[simp] theorem bar_mul_bar (g h : G) :
    bar D g * bar D h = bar D (g * h) := by
  ext <;> simp [bar, D.row_normalized, D.col_normalized, mul_assoc]

@[simp] theorem bar_one : bar D (1 : G) = e D := by
  rfl

@[simp] theorem e_mul_e : e D * e D = e D := by
  ext <;> simp [e, D.row_normalized, D.col_normalized]

/-- Normalization gives `x e=(i,g,1)`. -/
@[simp] theorem mul_e (x : ReesMatrix D) :
    x * e D = ⟨x.row, x.group, D.col0⟩ := by
  ext <;> simp [e, D.col_normalized]

/-- Normalization gives `e x=(1,g,lambda)`. -/
@[simp] theorem e_mul (x : ReesMatrix D) :
    e D * x = ⟨D.row0, x.group, x.col⟩ := by
  ext <;> simp [e, D.row_normalized]

/-- Compression by the distinguished idempotent gives `e x e=bar(g)`. -/
@[simp] theorem compress (x : ReesMatrix D) :
    e D * x * e D = bar D x.group := by
  rw [e_mul, mul_e]
  rfl

/-- Compatible tolerance for a semigroup (no global identity is required). -/
def IsSemigroupCompatibleTolerance
    {S : Type*} [Semigroup S] (tau : S → S → Prop) : Prop :=
  (∀ x, tau x x) ∧
  (∀ x y, tau x y → tau y x) ∧
  (∀ x y u v, tau x y → tau u v → tau (x * u) (y * v))

/-- Restriction of a local tolerance to the distinguished maximal subgroup. -/
def barRelation (tau : ReesMatrix D → ReesMatrix D → Prop) : G → G → Prop :=
  fun g h => tau (bar D g) (bar D h)

/-- The induced relation on the distinguished group is a compatible tolerance. -/
theorem barRelation_isCompatibleTolerance
    (tau : ReesMatrix D → ReesMatrix D → Prop)
    (htau : IsSemigroupCompatibleTolerance tau) :
    IsCompatibleTolerance (barRelation D tau) := by
  constructor
  · intro g
    exact htau.1 (bar D g)
  constructor
  · intro g h hgh
    exact htau.2.1 _ _ hgh
  · intro g h u v hgh huv
    change tau (bar D (g * u)) (bar D (h * v))
    rw [← bar_mul_bar D, ← bar_mul_bar D]
    exact htau.2.2 _ _ _ _ hgh huv

/--
Compressing a related pair by the distinguished idempotent preserves the
relation, yielding `bar g tau bar h`.
-/
theorem compressed_related
    (tau : ReesMatrix D → ReesMatrix D → Prop)
    (htau : IsSemigroupCompatibleTolerance tau)
    {x y : ReesMatrix D} (hxy : tau x y) :
    tau (bar D x.group) (bar D y.group) := by
  have he : tau (e D) (e D) := htau.1 (e D)
  have hleft : tau (e D * x) (e D * y) := htau.2.2 _ _ _ _ he hxy
  have hboth : tau ((e D * x) * e D) ((e D * y) * e D) :=
    htau.2.2 _ _ _ _ hleft he
  simpa [bar] using hboth

/-- The right defect `h^{-1}g` belongs to the local kernel. -/
theorem right_defect_mem_kernel
    (tau : ReesMatrix D → ReesMatrix D → Prop)
    (htau : IsSemigroupCompatibleTolerance tau)
    {x y : ReesMatrix D} (hxy : tau x y) :
    y.group⁻¹ * x.group ∈
      toleranceKernelSubgroup (barRelation D tau)
        (barRelation_isCompatibleTolerance D tau htau) := by
  change tau (bar D 1) (bar D (y.group⁻¹ * x.group))
  have hbar : tau (bar D x.group) (bar D y.group) :=
    compressed_related D tau htau hxy
  have hsym : tau (bar D y.group) (bar D x.group) := htau.2.1 _ _ hbar
  have href : tau (bar D y.group⁻¹) (bar D y.group⁻¹) := htau.1 _
  have hmul := htau.2.2 _ _ _ _ href hsym
  simpa using hmul

/-- The left defect `g h^{-1}` belongs to the local kernel. -/
theorem left_defect_mem_kernel
    (tau : ReesMatrix D → ReesMatrix D → Prop)
    (htau : IsSemigroupCompatibleTolerance tau)
    {x y : ReesMatrix D} (hxy : tau x y) :
    x.group * y.group⁻¹ ∈
      toleranceKernelSubgroup (barRelation D tau)
        (barRelation_isCompatibleTolerance D tau htau) := by
  change tau (bar D 1) (bar D (x.group * y.group⁻¹))
  have hbar : tau (bar D x.group) (bar D y.group) :=
    compressed_related D tau htau hxy
  have href : tau (bar D y.group⁻¹) (bar D y.group⁻¹) := htau.1 _
  have hmul := htau.2.2 _ _ _ _ hbar href
  have hrev := htau.2.1 _ _ hmul
  simpa using hrev

/-- Equality `x e = y bar(d)` forces equality of Rees rows. -/
theorem row_eq_of_mul_e_eq
    {x y : ReesMatrix D} {d : G}
    (h : x * e D = y * bar D d) : x.row = y.row := by
  have hr := congrArg (fun z : ReesMatrix D => z.row) h
  simpa using hr

/-- Equality `e x = bar(d) y` forces equality of Rees columns. -/
theorem col_eq_of_e_mul_eq
    {x y : ReesMatrix D} {d : G}
    (h : e D * x = bar D d * y) : x.col = y.col := by
  have hc := congrArg (fun z : ReesMatrix D => z.col) h
  simpa using hc

/--
Algebraic core of Lemma `cr:lem:index-rigidity`.  The two equalities are the
outputs of the manuscript's equalizing-context principle; the remaining
kernel and index conclusions are verified here from normalized Rees algebra.
-/
theorem local_index_rigidity_core
    (tau : ReesMatrix D → ReesMatrix D → Prop)
    (htau : IsSemigroupCompatibleTolerance tau)
    {x y : ReesMatrix D} (hxy : tau x y)
    (hrow : x * e D = y * bar D (y.group⁻¹ * x.group))
    (hcol : e D * x = bar D (x.group * y.group⁻¹) * y) :
    x.row = y.row ∧ x.col = y.col ∧
      x.group * y.group⁻¹ ∈
        toleranceKernelSubgroup (barRelation D tau)
          (barRelation_isCompatibleTolerance D tau htau) := by
  exact ⟨row_eq_of_mul_e_eq D hrow,
    col_eq_of_e_mul_eq D hcol,
    left_defect_mem_kernel D tau htau hxy⟩

/-- Central translation `nu(n)(i,g,lambda)=(i,ng,lambda)`. -/
def centralTranslate (n : G) (x : ReesMatrix D) : ReesMatrix D :=
  ⟨x.row, n * x.group, x.col⟩

@[simp] theorem centralTranslate_row (n : G) (x : ReesMatrix D) :
    (centralTranslate D n x).row = x.row := rfl
@[simp] theorem centralTranslate_group (n : G) (x : ReesMatrix D) :
    (centralTranslate D n x).group = n * x.group := rfl
@[simp] theorem centralTranslate_col (n : G) (x : ReesMatrix D) :
    (centralTranslate D n x).col = x.col := rfl

/-- Composition law `nu(mn)=nu(m) o nu(n)`. -/
theorem centralTranslate_mul (m n : G) (x : ReesMatrix D) :
    centralTranslate D (m * n) x =
      centralTranslate D m (centralTranslate D n x) := by
  ext <;> simp [centralTranslate, mul_assoc]

@[simp] theorem centralTranslate_one (x : ReesMatrix D) :
    centralTranslate D (1 : G) x = x := by
  ext <;> simp [centralTranslate]

/-- Left half of (CT), which uses only associativity. -/
theorem centralTranslate_mul_left (n : G) (x y : ReesMatrix D) :
    centralTranslate D n x * y = centralTranslate D n (x * y) := by
  ext <;> simp [centralTranslate, mul_assoc]

/-- Right half of (CT); centrality of `n` moves it across the sandwich factor. -/
theorem centralTranslate_mul_right
    {n : G} (hn : n ∈ Subgroup.center G) (x y : ReesMatrix D) :
    x * centralTranslate D n y = centralTranslate D n (x * y) := by
  rw [Subgroup.mem_center_iff] at hn
  apply rees_ext D
  · rfl
  · have hx : x.group * n = n * x.group := hn x.group
    have hq : D.sandwich x.col y.row * n =
        n * D.sandwich x.col y.row := hn (D.sandwich x.col y.row)
    calc
      x.group * D.sandwich x.col y.row * (n * y.group) =
          x.group * (D.sandwich x.col y.row * n) * y.group := by
            simp [mul_assoc]
      _ = x.group * (n * D.sandwich x.col y.row) * y.group := by rw [hq]
      _ = (x.group * n) * D.sandwich x.col y.row * y.group := by
            simp [mul_assoc]
      _ = (n * x.group) * D.sandwich x.col y.row * y.group := by rw [hx]
      _ = n * (x.group * D.sandwich x.col y.row * y.group) := by
            simp [mul_assoc]
  · rfl

/-- The central-translation action is free. -/
theorem centralTranslate_free {m n : G} {x : ReesMatrix D}
    (h : centralTranslate D m x = centralTranslate D n x) : m = n := by
  have hg := congrArg (fun z : ReesMatrix D => z.group) h
  simp only [centralTranslate_group] at hg
  exact mul_right_cancel hg

end ReesMatrix

end SCLCompression
end LeanCfgProject
