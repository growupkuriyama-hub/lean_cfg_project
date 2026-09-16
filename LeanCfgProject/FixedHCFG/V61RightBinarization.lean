import LeanCfgProject.FixedHCFG.V61NormalizationEndToEnd

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
A constructive right-binarization lemma for Appendix A of TCS revision v61.

The preceding `V61BlockDerivation` file records the invariant that every
intermediate symbol represents a contiguous block of an original right-hand
side.  Here we prove that the standard right-associated binarization pattern
actually builds such a block derivation from singleton atom leaves.
-/

namespace V61RightBinarization

variable {N0 : Type v} {NB : Type w} {Sigma : Type u}
variable {epsilon : V61EpsilonRules NB}
variable {terminal : V60TerminalRules NB Sigma}
variable {unit : V61UnitRules NB}
variable {binary : V60BinaryRules NB}
variable {embed : N0 → NB}
variable {sourceTree : ∀ A : N0,
  V61NullableDerivationTree epsilon terminal unit binary (embed A)}

/--
Terminal isolation and embedding of source nonterminals provide a singleton
block derivation for every source atom.
-/
def atom_leaf_block
    (leaf : V61SourceAtom N0 Sigma → NB)
    (hNonterminal : ∀ A : N0,
      leaf (V61SourceAtom.nonterminal A) = embed A)
    (hTerminal : ∀ a : Sigma,
      terminal (leaf (V61SourceAtom.terminal a)) a)
    (a : V61SourceAtom N0 Sigma) :
    V61BlockDerivation epsilon terminal unit binary embed sourceTree
      (leaf a) [a] := by
  cases a with
  | nonterminal A =>
      rw [hNonterminal A]
      exact .source A
  | terminal a =>
      exact .term (leaf (V61SourceAtom.terminal a)) a (hTerminal a)

/--
Generic right-associated chain.  `node xs` is the nonterminal assigned to the
contiguous block `xs`; a block of length at least two splits into its first
atom and its remaining suffix.  This exactly matches the usual binarization
chain for one original right-hand side.
-/
def right_chain_block
    (leaf : V61SourceAtom N0 Sigma → NB)
    (node : List (V61SourceAtom N0 Sigma) → NB)
    (hLeaf : ∀ a : V61SourceAtom N0 Sigma,
      V61BlockDerivation epsilon terminal unit binary embed sourceTree
        (leaf a) [a])
    (hEmpty : epsilon (node []))
    (hSingleton : ∀ a : V61SourceAtom N0 Sigma,
      unit (node [a]) (leaf a))
    (hCons : ∀ (a b : V61SourceAtom N0 Sigma)
        (rest : List (V61SourceAtom N0 Sigma)),
      binary (node (a :: b :: rest)) (leaf a) (node (b :: rest)))
    (atoms : List (V61SourceAtom N0 Sigma)) :
    V61BlockDerivation epsilon terminal unit binary embed sourceTree
      (node atoms) atoms := by
  induction atoms with
  | nil =>
      exact .eps (node []) hEmpty
  | cons a rest ih =>
      cases rest with
      | nil =>
          exact .stepUnit (hSingleton a) (hLeaf a)
      | cons b rest =>
          exact .combine (hCons a b rest) (hLeaf a) ih

/--
Right-binarization block invariant obtained directly from the concrete
terminal-isolation leaf rules.  This is the form intended for the forthcoming
raw-production normalization constructor.
-/
def right_chain_block_of_isolated_atoms
    (leaf : V61SourceAtom N0 Sigma → NB)
    (node : List (V61SourceAtom N0 Sigma) → NB)
    (hNonterminal : ∀ A : N0,
      leaf (V61SourceAtom.nonterminal A) = embed A)
    (hTerminal : ∀ a : Sigma,
      terminal (leaf (V61SourceAtom.terminal a)) a)
    (hEmpty : epsilon (node []))
    (hSingleton : ∀ a : V61SourceAtom N0 Sigma,
      unit (node [a]) (leaf a))
    (hCons : ∀ (a b : V61SourceAtom N0 Sigma)
        (rest : List (V61SourceAtom N0 Sigma)),
      binary (node (a :: b :: rest)) (leaf a) (node (b :: rest)))
    (atoms : List (V61SourceAtom N0 Sigma)) :
    V61BlockDerivation epsilon terminal unit binary embed sourceTree
      (node atoms) atoms := by
  apply right_chain_block leaf node
  · exact atom_leaf_block leaf hNonterminal hTerminal
  · exact hEmpty
  · exact hSingleton
  · exact hCons

/--
Count-compatible suffix-chain builder.  Standard right binarization needs a
fresh chain symbol only for suffixes of length at least two.  The length-two
suffix closes directly with two atom leaves, and longer suffixes recurse on the
proper tail.  Thus no artificial empty or singleton chain symbols are needed.
-/
def right_suffix_block
    (leaf : V61SourceAtom N0 Sigma → NB)
    (node : List (V61SourceAtom N0 Sigma) → NB)
    (hLeaf : ∀ a : V61SourceAtom N0 Sigma,
      V61BlockDerivation epsilon terminal unit binary embed sourceTree
        (leaf a) [a])
    (hPair : ∀ a b : V61SourceAtom N0 Sigma,
      binary (node [a, b]) (leaf a) (leaf b))
    (hLong : ∀ (a b c : V61SourceAtom N0 Sigma)
        (rest : List (V61SourceAtom N0 Sigma)),
      binary (node (a :: b :: c :: rest))
        (leaf a) (node (b :: c :: rest)))
    (atoms : List (V61SourceAtom N0 Sigma))
    (hTwo : 2 ≤ atoms.length) :
    V61BlockDerivation epsilon terminal unit binary embed sourceTree
      (node atoms) atoms := by
  cases atoms with
  | nil => omega
  | cons a rest =>
      cases rest with
      | nil => omega
      | cons b rest =>
          cases rest with
          | nil =>
              exact .combine (hPair a b) (hLeaf a) (hLeaf b)
          | cons c rest =>
              exact .combine (hLong a b c rest) (hLeaf a)
                (right_suffix_block leaf node hLeaf hPair hLong
                  (b :: c :: rest) (by simp))
termination_by atoms.length

/--
Concrete terminal-isolation version of `right_suffix_block`.
-/
def right_suffix_block_of_isolated_atoms
    (leaf : V61SourceAtom N0 Sigma → NB)
    (node : List (V61SourceAtom N0 Sigma) → NB)
    (hNonterminal : ∀ A : N0,
      leaf (V61SourceAtom.nonterminal A) = embed A)
    (hTerminal : ∀ a : Sigma,
      terminal (leaf (V61SourceAtom.terminal a)) a)
    (hPair : ∀ a b : V61SourceAtom N0 Sigma,
      binary (node [a, b]) (leaf a) (leaf b))
    (hLong : ∀ (a b c : V61SourceAtom N0 Sigma)
        (rest : List (V61SourceAtom N0 Sigma)),
      binary (node (a :: b :: c :: rest))
        (leaf a) (node (b :: c :: rest)))
    (atoms : List (V61SourceAtom N0 Sigma))
    (hTwo : 2 ≤ atoms.length) :
    V61BlockDerivation epsilon terminal unit binary embed sourceTree
      (node atoms) atoms := by
  exact right_suffix_block leaf node
    (atom_leaf_block leaf hNonterminal hTerminal)
    hPair hLong atoms hTwo

/--
Every suffix-node in the older unrestricted right-associated chain therefore
carries the expected contiguous suffix block, not merely the full production
root.
-/
def suffix_block_of_right_chain
    (leaf : V61SourceAtom N0 Sigma → NB)
    (node : List (V61SourceAtom N0 Sigma) → NB)
    (hNonterminal : ∀ A : N0,
      leaf (V61SourceAtom.nonterminal A) = embed A)
    (hTerminal : ∀ a : Sigma,
      terminal (leaf (V61SourceAtom.terminal a)) a)
    (hEmpty : epsilon (node []))
    (hSingleton : ∀ a : V61SourceAtom N0 Sigma,
      unit (node [a]) (leaf a))
    (hCons : ∀ (a b : V61SourceAtom N0 Sigma)
        (rest : List (V61SourceAtom N0 Sigma)),
      binary (node (a :: b :: rest)) (leaf a) (node (b :: rest)))
    (suffix : List (V61SourceAtom N0 Sigma)) :
    V61BlockDerivation epsilon terminal unit binary embed sourceTree
      (node suffix) suffix := by
  exact right_chain_block_of_isolated_atoms
    leaf node hNonterminal hTerminal hEmpty hSingleton hCons suffix

end V61RightBinarization

end FixedHCFG
end LeanCfgProject
