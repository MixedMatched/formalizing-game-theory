import Mathlib.Data.Real.Basic
import Aesop

-- a Utility is a Real number representing the payoff of a given set of strategies
structure Utility := (val : Real)

instance : Add Utility := ⟨λ u v => ⟨u.val + v.val⟩⟩
instance : LE Utility := ⟨λ u v => u.val ≤ v.val⟩
instance : LT Utility := ⟨λ u v => u.val < v.val⟩

-- a PureStrategy is an instance of the strategy type
structure PureStrategy (A : Type) := (val : A)

-- a MixedStrategy is a probability distribution over PureStrategies
structure MixedStrategy (A : Type) :=
  (strategies: List A)
  (probabilities: List Real)
  (probabilities_sum_to_one: List.foldl (a + b) 0 probabilities = 1)
  (same_length: List.length strategies = List.length probabilities)

-- a Strategy is either a PureStrategy or a MixedStrategy
inductive Strategy (A : Type) where
| pure : PureStrategy A → Strategy A
| mixed : MixedStrategy A → Strategy A

-- a StrategyProfile is a list of strategies (for type reasons, we need to use a function)
structure StrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → Strategy (List.get L i))

-- a UtilityFunction is a function that takes a StrategyProfile and returns a Utility
structure UtilityFunction (L: List Type) where
  (val: StrategyProfile L → List Utility)

-- a Game is a number of players, a list of strategies for each player, and a utility function
structure Game (L: List Type) (N: Nat) where
  (utility: UtilityFunction L)
  (same_length: (List.length L) = N)
  (at_least_one_player: N > 0)

-- a PlayGame is a function that takes a Game, a StrategyProfile, and returns a list of Utilities
def PlayGame (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : List Utility := G.utility.val S

-- NashEquilibrium is a StrategyProfile where no player can increase their utility by unilaterally changing their strategy
def NashEquilibrium (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : Prop :=
  ∀ (i: Fin (List.length L))
    (s': Strategy (List.get L i)),
    let newStrategies : (f: Fin (List.length L)) → Strategy (List.get L f) :=
      λ j => if h : i = j then by { rw [h] at s'; exact s' }
                          else S.strategies j
    let newStrategyProfile : StrategyProfile L := { strategies := @newStrategies }
    PlayGame L N G newStrategyProfile ≤ PlayGame L N G S
