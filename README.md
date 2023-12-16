# Formalizing Game Theory in Lean

Formalizing Game Theory in the Lean proof language holds significant promise for advancing both the theoretical foundations and practical applications of game-theoretic models. Lean, known for its precision and rigor in formal verification, offers a robust framework for expressing and proving mathematical theorems. By formalizing Game Theory in Lean, researchers and practitioners can establish a rigorous basis for analyzing strategic interactions, ensuring the correctness of game-theoretic concepts, and facilitating automated verification of complex game structures. 

This repository contains an example of formal structures and properties to represent and reason about games in Lean. While there have been other attempts to make such a formalization, the representation proposed here is novel in that it can represent a much broader class of games than previous attempts. In particular, this formalization is able to represent games with more than 2 players, games with a continuous set of actions, and games with intricate utility functions.

## Formalization

Our formalization starts with a definition of Utility as:

```lean
structure Utility := (val : Real)
```

which defines Utility as a real number. While many different types could be used to represent preference order, we chose to restrict the formalization to real numbers because they are a common choice in the literature and because they are easy to work with in Lean.

We then represent a Pure Strategy as:

```lean
structure PureStrategy (A : Type) := (val : A)
```

which defines a Pure Strategy as an instance of some type `A`. This means that a player's available strategies are defined with a type `A`, and an individual strategy is defined as an instance of that type. For example, in the game of Stag Hunt, the avalable strategies could be formalized as the type:

```lean
inductive StagHuntStrategies
| stag
| hare
```

and a strategy for player 1 could be formalized as the instance `PureStrategy StagHuntStrategies.stag`. This representation allows for a wide variety of games to be formalized, including games with a continuous set of actions. For example, the Nash Demand Game could be formalized with the type:

```lean
structure NashDemandStrategies :=
    (demand : Real)
    (above_0: demand > 0)
    (below_1: demand < 1)
```

and a strategy for player 1 could be formalized as the instance `PureStrategy (NashDemandStrategies 0.5 ... ...)`.

We then represent a Mixed Strategy as:

```lean
structure MixedStrategy (A : Type) :=
  (strategies: List A)
  (probabilities: List Real)
  (probabilities_sum_to_one: List.foldl (a + b) 0 probabilities = 1)
  (same_length: List.length strategies = List.length probabilities)
```

which defines a Mixed Strategy as a list of Pure Strategies and a list of probabilities. 

Then, a Strategy is defined as either a Pure Strategy or a Mixed Strategy:

```lean
inductive Strategy (A : Type) where
| pure : PureStrategy A → Strategy A
| mixed : MixedStrategy A → Strategy A
```

A Strategy Profile, which is a list of strategies, is then defined as:

```lean
structure StrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → Strategy (List.get L i))
```

The reason that this must be a function from a natural number to a strategy is that the strategies for each player must be of different types. For example, in the Ultimatum Game, the first player's strategy is a real number between 0 and 1, while the second player's strategy is a essentially a reject or accept answer.

A Utility Profile, which is a list of utilities, is then defined as:

```lean
structure UtilityProfile (L: List Type) where
  (utilities: List Utility)
  (same_length: List.length L = List.length utilities)
```

And the Utility Function is defined as:

```lean
structure UtilityFunction (L: List Type) where
  (val: StrategyProfile L → UtilityProfile L)
```

which essentially maps a Strategy Profile to a Utility Profile.

Finally, a Game is defined as:

```lean
structure Game (L: List Type) (N: Nat) where
  (utility: UtilityFunction L)
  (same_length: (List.length L) = N)
  (at_least_one_player: N > 0)
```

and an instance of a Game is defined as:

```lean
def PlayGame (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : UtilityProfile L := G.utility.val S
```

which applies the utility function of the game to a given strategy profile to get a utility profile.

We also define a property of a Strategy Profile being a Nash Equilibrium as:

```lean
def NashEquilibrium (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : Prop :=
  ∀ (i: Fin (List.length L))
    (s': Strategy (List.get L i)),
    let newStrategies : (f: Fin (List.length L)) → Strategy (List.get L f) :=
      λ j => if h : i = j then by { rw [h] at s'; exact s' }
                          else S.strategies j
    let newStrategyProfile : StrategyProfile L := { strategies := @newStrategies }
    let UNew : UtilityProfile L := PlayGame L N G newStrategyProfile
    let UOld : UtilityProfile L := PlayGame L N G S
    (List.get UNew.utilities (Fin.cast UNew.same_length i)) ≤ (List.get UOld.utilities (Fin.cast UOld.same_length i))
```

which essentially states that, for each player, and for each strategy that the player could switch to, the utility of that player in the new strategy is less than or equal to their utility in the original strategy profile.

## Example: Prisoner's Dilemma

The Prisoner's Dilemma is a classic game in Game Theory. It is a two-player game where each player can either cooperate or defect. An example payoff matrix which fits the definition of Prisoner's Dilemma is:

| Player 1 / Player 2 | Cooperate | Defect |
| ------------------- | --------- | ------ |
| Cooperate           | 4, 4      | 1, 6   |
| Defect              | 6, 1      | 2, 2   |

We created an example formalization of the Prisoner's Dilemma in Lean as follows:

```lean
inductive PrisonersDilemmaStrategies
| silent
| confess

def PL : List Type := [PrisonersDilemmaStrategies, PrisonersDilemmaStrategies]
def PL_length : List.length PL = 2 := rfl

def PrisonersDilemmaUtilityFunction : UtilityFunction PL :=
  { val := λ S => match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
                  | Strategy.pure s1, Strategy.pure s2 =>
                    have h1 : PureStrategy (List.get PL (Fin.ofNat 0)) = PureStrategy PrisonersDilemmaStrategies := rfl
                    have h2 : PureStrategy (List.get PL (Fin.ofNat 1)) = PureStrategy PrisonersDilemmaStrategies := rfl
                    let s1' : PureStrategy PrisonersDilemmaStrategies := by { rw [←h1]; exact s1 }
                    let s2' : PureStrategy PrisonersDilemmaStrategies := by { rw [←h2]; exact s2 }
                    match s1'.val, s2'.val with
                    | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.silent  => { utilities := [4, 4], same_length := rfl }
                    | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.confess => { utilities := [1, 6], same_length := rfl }
                    | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.silent  => { utilities := [6, 1], same_length := rfl }
                    | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.confess => { utilities := [2, 2], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

def PrisonersDilemmaGame : Game PL 2 :=
  { utility := PrisonersDilemmaUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }
```

This formalization defines the type `PrisonersDilemmaStrategies` to be the type of strategies for the Prisoner's Dilemma, and defines the list `PL` to be the Strategy to Player mapping. It then defines the utility function for the Prisoner's Dilemma by matching on the strategies of the two players and returning the appropriate utility profile. Finally, it defines the Prisoner's Dilemma game as a game with the Prisoner's Dilemma utility function, 2 players, and a proof that there is at least one player.

## Example: Rock, Paper, Scissors

Rock, Paper, Scissors is another classic game. It's a two-player game with 3 strategies for each player. An example payoff matrix which fits the definition of Rock, Paper, Scissors is:

| Player 1 / Player 2 | Rock | Paper | Scissors |
| ------------------- | ---- | ----- | -------- |
| Rock                | 1, 1 | 0, 2  | 2, 0     |
| Paper               | 2, 0 | 1, 1  | 0, 2     |
| Scissors            | 0, 2 | 2, 0  | 1, 1     |

We created an example formalization of Rock, Paper, Scissors in Lean as follows:

```lean
inductive RockPaperScissorsStrategies where
| rock
| paper
| scissors

def RPS : List Type := [RockPaperScissorsStrategies, RockPaperScissorsStrategies]
def RPS_length : List.length RPS = 2 := rfl

def RockPaperScissorsUtilityFunction : UtilityFunction RPS :=
  { val := λ S => match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
                  | Strategy.pure s1, Strategy.pure s2 =>
                    have h1 : PureStrategy (List.get RPS (Fin.ofNat 0)) = PureStrategy RockPaperScissorsStrategies := rfl
                    have h2 : PureStrategy (List.get RPS (Fin.ofNat 1)) = PureStrategy RockPaperScissorsStrategies := rfl
                    let s1' : PureStrategy RockPaperScissorsStrategies := by { rw [←h1]; exact s1 }
                    let s2' : PureStrategy RockPaperScissorsStrategies := by { rw [←h2]; exact s2 }
                    match s1'.val, s2'.val with
                    | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.rock     => { utilities := [1, 1], same_length := rfl }
                    | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.paper    => { utilities := [0, 2], same_length := rfl }
                    | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.scissors => { utilities := [2, 0], same_length := rfl }
                    | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.rock     => { utilities := [2, 0], same_length := rfl }
                    | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.paper    => { utilities := [1, 1], same_length := rfl }
                    | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.scissors => { utilities := [0, 2], same_length := rfl }
                    | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.rock     => { utilities := [0, 2], same_length := rfl }
                    | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.paper    => { utilities := [2, 0], same_length := rfl }
                    | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.scissors => { utilities := [1, 1], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

def RockPaperScissorsGame : Game RPS 2 :=
  { utility := RockPaperScissorsUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }
```

This formalization defines the type `RockPaperScissorsStrategies` to be the type of strategies for Rock, Paper, Scissors, and defines the list `RPS` to be the Strategy to Player mapping. It then defines the utility function for Rock, Paper, Scissors by matching on the strategies of the two players and returning the appropriate utility profile. Finally, it defines the Rock, Paper, Scissors game as a game with the Rock, Paper, Scissors utility function, 2 players, and a proof that there is at least one player.

## Example: Nash Demand Game

Our last example is the Nash Demand Game. It's a two-player game where each player can demand a real number between 0 and 1. If the sum of the demands is greater than 1, then both players get 0. Otherwise, the first player gets their demand and the second player gets theirs.

We created an example formalization of the Nash Demand Game in Lean as follows:

```lean
structure NashDemandChoice where
  (demand: Real)
  (demand_nonnegative: demand ≥ 0)
  (demand_le_one: demand ≤ 1)

def NashDemandChoiceList : List Type := [NashDemandChoice, NashDemandChoice]

noncomputable def NashDemandUtilityFunction : UtilityFunction NashDemandChoiceList :=
  { val := λ S => match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
                  | Strategy.pure s1, Strategy.pure s2 =>
                    have h1 : PureStrategy (List.get NashDemandChoiceList (Fin.ofNat 0)) = PureStrategy NashDemandChoice := rfl
                    have h2 : PureStrategy (List.get NashDemandChoiceList (Fin.ofNat 1)) = PureStrategy NashDemandChoice := rfl
                    let s1' : PureStrategy NashDemandChoice := by { rw [←h1]; exact s1 }
                    let s2' : PureStrategy NashDemandChoice := by { rw [←h2]; exact s2 }
                    match s1', s2' with
                    | ⟨d1, _, _⟩, ⟨d2, _, _⟩ =>
                      let d12 : Utility := ⟨d1 + d2⟩
                      let oneUtility : Utility := ⟨1⟩
                        if d12 ≤ oneUtility then { utilities := [⟨d1⟩, ⟨d2⟩], same_length := rfl }
                      else { utilities := [0, 0], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

noncomputable def NashDemandGame : Game NashDemandChoiceList 2 :=
  { utility := NashDemandUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }
```

This formalization defines the type `NashDemandChoice` to be the type of strategies for the Nash Demand Game, and defines the list `NashDemandChoiceList` to be the Strategy to Player mapping. It then defines the utility function for the Nash Demand Game by matching on the strategies of the two players and returning the appropriate utility profile. Finally, it defines the Nash Demand Game as a game with the Nash Demand utility function, 2 players, and a proof that there is at least one player.

## Conclusion

This repository contains an example of formal structures and properties to represent and reason about games in Lean. While there have been other attempts to make such a formalization, the representation proposed here is novel in that it can represent a much broader class of games than previous attempts. In particular, this formalization is able to represent games with more than 2 players, games with a continuous set of actions, and games with intricate utility functions.