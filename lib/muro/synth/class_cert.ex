defmodule Muro.Synth.ClassCert do
  @moduledoc false

  # A reach-family survivor is optimal for a binary placement MDP by one
  # truth table over its atoms. The table does not mention states. Any
  # other survivor keeps the cover split. This book does not call a Finder.

  alias Muro.Synth.Cert

  @atom_cap 16
  # A cover this small still gets the per-state agreement table. queens4
  # has 18 states. A larger cover certifies from the recurrence: the
  # table and the per-state observation refls grow with the states, and
  # the class lemma does not.
  @agreement_cap 64
  @bad "the reach-family ranking prefers an action that does not reach while another action does"
  @stems ["reaches-pos", "has-pos-reward"]
  @placement Path.expand("../../../examples/cshrl/lib/placement.muro", __DIR__)
  @need ~w(board-blocked board-full board-extend board-length board-column board-snoc board-same board-judge horizon bottom all-actions step)

  @doc false
  # True when this ranking will be a class proof and the cover is too
  # large for the per-state agreement. The reach runs then stay the
  # recurrence, and the book does not emit a hold per state.
  def recur_only?(host, arms, oracle) when is_list(arms) and is_binary(oracle) do
    actions = ctors(host, "Action")

    oracle != "successor" and arms != [] and actions != [] and
      Enum.all?(arms, &family?(&1.pred, actions)) and
      Enum.all?(
        arms,
        &(is_binary(&1.action) and is_binary(&1.else) and &1.action in actions and
            &1.else in actions)
      ) and
      placement?(host, actions) and cover_count(host) > @agreement_cap
  end

  def render(host, arms, oracle, bound) do
    actions = ctors(host, "Action")

    cond do
      reason = Process.get(:muro_synth_class_refusal) ->
        {:skip, reason}

      oracle == "successor" or arms == [] ->
        :fallthrough

      not Enum.all?(arms, &family?(&1.pred, actions)) ->
        :fallthrough

      not placement?(host, actions) ->
        :fallthrough

      not dyn?(bound) ->
        :fallthrough

      not Enum.all?(arms, &(&1.action in actions and &1.else in actions)) ->
        :fallthrough

      true ->
        case scan(actions, arms) do
          {:skip, reason} -> {:skip, reason}
          :ok -> emit(host, arms, bound, actions)
        end
    end
  end

  @doc false
  def family?(pred, actions) when is_list(actions), do: family_pred?(pred, actions)

  @doc false
  def scan(actions, arms) when is_list(actions) and is_list(arms) do
    cond do
      arms == [] or not Enum.all?(arms, &family?(&1.pred, actions)) ->
        :ok

      not Enum.all?(arms, &(&1.action in actions and &1.else in actions)) ->
        :ok

      true ->
        atoms = atoms_of(actions, arms)

        cond do
          length(atoms) > @atom_cap ->
            {:skip, "the reach-family truth table has #{length(atoms)} atoms"}

          bad?(actions, arms, atoms) ->
            {:skip, @bad}

          true ->
            :ok
        end
    end
  end

  defp emit(host, arms, bound, actions) do
    reward = solved_reward(File.read!(host.path))
    dyn = bound.dyn
    atoms = atoms_of(actions, arms)
    hyps = hyps(atoms)
    names = bound.names

    ctx = %{
      actions: actions,
      atoms: atoms,
      hyps: hyps,
      arms: arms,
      bound: bound,
      names: names,
      one: dyn.one,
      pos: dyn.pos,
      best: dyn.best,
      any: dyn.any,
      orb: names.orb,
      andb: names.andb,
      notb: names.notb,
      lor: "class-orb-true",
      lof: "class-orb-false",
      lat: "class-andb-true",
      laf: "class-andb-false",
      lnt: "class-notb-true",
      lnf: "class-notb-false",
      bits: %{},
      index: nil,
      winner: nil,
      goal: nil,
      eq_true: nil,
      eq_false: []
    }

    text =
      [
        "-- Class proof of the synthesized reach-family ranking.\n" <>
          "-- It does not use a Finder and it does not split the cover.\n" <>
          if(Process.get(:muro_synth_class_recur) == true,
            do: "-- The cover is past the per-state agreement, so the proof is the recurrence.\n",
            else: ""
          ),
        hypotheses(actions, reward),
        transport(names),
        tie_lemmas(),
        bridge_eqs(dyn),
        reach_defs(actions, dyn),
        conflict_def(dyn),
        arm_eqs(arms, bound, ctx),
        rank_def(bound, arms, actions),
        named_ranks(arms, bound, actions),
        win_defs(arms, actions, bound, ctx),
        apply_def(arms, bound, actions),
        preserves_def()
      ]
      |> Enum.join("\n")

    {:ok,
     %{
       text: text,
       obligations: [],
       certificate: "CoindHomo",
       also: nil,
       imports: [@placement],
       class_proof: true
     }}
  end

  defp placement?(host, actions) do
    src = File.read!(host.path)

    Enum.all?(@need, &defined?(host, &1)) and
      ctors(host, "State") == ["ongoing", "dead", "solved"] and
      actions == host.actions and actions != [] and
      String.contains?(src, "def bottom : run Reward := 0") and
      String.contains?(src, "def Reward : spec Type := Nat") and solved_reward(src) != nil
  end

  defp solved_reward(src) do
    case Regex.run(~r/solved\s+\w+\s*,\s*(\d+)/, src) do
      [_, n] ->
        k = String.to_integer(n)
        if k > 0, do: k, else: nil

      _ ->
        nil
    end
  end

  defp dyn?(%{dyn: %{one: one, pos: pos, best: best, any: any}})
       when is_binary(one) and is_binary(pos) and is_binary(best) and is_binary(any),
       do: true

  defp dyn?(_), do: false

  defp cover_count(host) do
    case host[:all_states] do
      states when is_list(states) -> length(states)
      _ -> 0
    end
  end

  defp defined?(host, name), do: Enum.any?(host.book, &(Map.get(&1, :name) == name))

  defp ctors(host, data) do
    case Enum.find(host.book, &(Map.get(&1, :kind) == :data and &1.name == data)) do
      %{ctors: ctors} -> Enum.map(ctors, & &1.name)
      _ -> []
    end
  end

  defp hypotheses(actions, reward) do
    branches =
      Enum.map_join(actions, "\n", fn action ->
        "      | #{action} => #{elem_proof(actions, action)}"
      end)

    """
    def Config : spec Type := List Nat
    def solved-reward : run Reward := #{reward}
    def class-dead : run State := dead
    def class-ongoing : run Π (c : Config) → State :=
      λ (c : Config) → ongoing c
    def class-solved : run Π (c : Config) → State :=
      λ (c : Config) → solved c
    def class-blocked : run Π (+ c : Config) → Bool := board-blocked
    def class-full : run Π (c : Config) → Bool := board-full
    def class-place : run Π (+ c : Config) → Π (+ a : Action) → Config := board-extend
    def class-length : run Π (c : Config) → Nat := board-length

    def state-view : evidence Π (s : State) → StateView s :=
      λ (s : State) →
        match s motive (λ (t : State) → StateView t)
          | ongoing c => view-ongoing c
          | dead => view-dead
          | solved c => view-solved c

    def zero-lt-R : evidence le (suc bottom) solved-reward := tt

    def board-same-nat : evidence Π (m : Nat) → Π (n : Nat) →
                                  {board-same m n ≡ nat-eq m n : Bool} :=
      λ (m : Nat) →
        match m motive (λ (x : Nat) → Π (n : Nat) → {board-same x n ≡ nat-eq x n : Bool})
          | 0 => λ (n : Nat) →
              match n motive (λ (y : Nat) → {board-same 0 y ≡ nat-eq 0 y : Bool})
                | 0 => refl
                | suc _ => refl
          | suc m1 => λ (n : Nat) →
              match n motive (λ (y : Nat) → {board-same (suc m1) y ≡ nat-eq (suc m1) y : Bool})
                | 0 => refl
                | suc n1 => board-same-nat m1 n1

    def full-is-length : evidence Π (c : Config) →
                                  {class-full c ≡ nat-eq (class-length c) horizon : Bool} :=
      λ (c : Config) → board-same-nat (class-length c) horizon

    def step-dead : evidence Π (a : Action) →
                             {step class-dead a ≡ (class-dead, bottom) : State × Reward} :=
      λ (a : Action) → refl

    def step-solved : evidence Π (c : Config) → Π (a : Action) →
                               {step (class-solved c) a ≡ (class-solved c, solved-reward) : State × Reward} :=
      λ (c : Config) → λ (a : Action) → refl

    def step-ongoing : evidence Π (c : Config) → Π (a : Action) →
                                {step (class-ongoing c) a ≡ class-judge (class-place c a) : State × Reward} :=
      λ (c : Config) → λ (a : Action) → refl

    def length-snoc : evidence Π (xs : List Nat) → Π (x : Nat) →
                               {board-length (board-snoc xs x) ≡ suc (board-length xs) : Nat} :=
      λ (xs : List Nat) → λ (x : Nat) →
        match xs motive (λ (ys : List Nat) → {board-length (board-snoc ys x) ≡ suc (board-length ys) : Nat})
          | nil => refl
          | cons y ys =>
              rewrite length-snoc ys x motive (λ z → {suc z ≡ suc (suc (board-length ys)) : Nat}) in
              refl

    def length-place : evidence Π (c : Config) → Π (a : Action) →
                                {class-length (class-place c a) ≡ suc (class-length c) : Nat} :=
      λ (c : Config) → λ (a : Action) → length-snoc c (board-column a)

    def in-actions : evidence Π (a : Action) → Elem a all-actions :=
      λ (a : Action) →
        match a motive (λ (x : Action) → Elem x all-actions)
    #{branches}
    """
  end

  defp elem_proof(actions, target), do: elem_from(actions, target)

  defp elem_from([target | rest], target), do: "elem-here #{target} #{list_term(rest)}"

  defp elem_from([head | rest], target) do
    "elem-there #{target} #{head} #{list_term(rest)} (#{elem_from(rest, target)})"
  end

  defp list_term([]), do: "nil"
  defp list_term([head | tail]), do: "(cons #{head} #{list_term(tail)})"

  defp transport(names) do
    o = names.orb
    a = names.andb
    n = names.notb

    """
    def class-orb-true : evidence Π (a : Bool) → Π (b : Bool) →
                                  Π (h : {a ≡ true : Bool}) →
                                  {#{o} a b ≡ true : Bool} :=
      λ (a : Bool) → λ (b : Bool) → λ (h : {a ≡ true : Bool}) →
        rewrite h motive (λ z → {#{o} z b ≡ true : Bool}) in refl

    def class-orb-false : evidence Π (a : Bool) → Π (b : Bool) → Π (c : Bool) →
                                   Π (ha : {a ≡ false : Bool}) →
                                   Π (hb : {b ≡ c : Bool}) →
                                   {#{o} a b ≡ c : Bool} :=
      λ (a : Bool) → λ (b : Bool) → λ (c : Bool) →
      λ (ha : {a ≡ false : Bool}) → λ (hb : {b ≡ c : Bool}) →
        rewrite ha motive (λ z → {#{o} z b ≡ c : Bool}) in
          (rewrite hb motive (λ z → {z ≡ c : Bool}) in refl)

    def class-andb-true : evidence Π (a : Bool) → Π (b : Bool) → Π (c : Bool) →
                                   Π (ha : {a ≡ true : Bool}) →
                                   Π (hb : {b ≡ c : Bool}) →
                                   {#{a} a b ≡ c : Bool} :=
      λ (a : Bool) → λ (b : Bool) → λ (c : Bool) →
      λ (ha : {a ≡ true : Bool}) → λ (hb : {b ≡ c : Bool}) →
        rewrite ha motive (λ z → {#{a} z b ≡ c : Bool}) in
          (rewrite hb motive (λ z → {z ≡ c : Bool}) in refl)

    def class-andb-false : evidence Π (a : Bool) → Π (b : Bool) →
                                    Π (h : {a ≡ false : Bool}) →
                                    {#{a} a b ≡ false : Bool} :=
      λ (a : Bool) → λ (b : Bool) → λ (h : {a ≡ false : Bool}) →
        rewrite h motive (λ z → {#{a} z b ≡ false : Bool}) in refl

    def class-notb-true : evidence Π (a : Bool) → Π (h : {a ≡ false : Bool}) →
                                   {#{n} a ≡ true : Bool} :=
      λ (a : Bool) → λ (h : {a ≡ false : Bool}) →
        rewrite h motive (λ z → {#{n} z ≡ true : Bool}) in refl

    def class-notb-false : evidence Π (a : Bool) → Π (h : {a ≡ true : Bool}) →
                                    {#{n} a ≡ false : Bool} :=
      λ (a : Bool) → λ (h : {a ≡ true : Bool}) →
        rewrite h motive (λ z → {#{n} z ≡ false : Bool}) in refl
    """
  end

  defp tie_lemmas do
    """
    def class-hit-ask : run Π (+ s : State) → Π (+ y : Action) → Bool :=
      λ (+ s : State) → λ (+ y : Action) → hit s y horizon

    def class-cons-false : evidence Π (+ ask : Π (+ y : Action) → Bool) →
                                    Π (+ x : Action) →
                                    Π (rest : List Action) →
                                    Π (hf : {ask x ≡ false : Bool}) →
                                    Π (hr : {hit-fold ask rest ≡ false : Bool}) →
                                    {hit-fold ask (cons x rest) ≡ false : Bool} :=
      λ (+ ask : Π (+ y : Action) → Bool) → λ (+ x : Action) → λ (rest : List Action) →
      λ (hf : {ask x ≡ false : Bool}) →
      λ (hr : {hit-fold ask rest ≡ false : Bool}) →
        rewrite (fold-cons-eq ask x rest)
          motive (λ z → {z ≡ false : Bool})
        in
        rewrite hf
          motive (λ b →
            {(match b motive (λ _ → Bool)
               | true => true
               | false => hit-fold ask rest) ≡ false : Bool})
        in hr
    """
  end

  defp bridge_eqs(dyn) do
    """
    def class-pos-eq : evidence Π (q : Reward) → {#{dyn.pos} q ≡ class-pos q : Bool} :=
      λ (q : Reward) →
        match q motive (λ x → {#{dyn.pos} x ≡ class-pos x : Bool})
          | 0 => refl
          | suc _ => refl

    def class-best-eq : evidence Π (+ t : State) → Π (+ n : Nat) →
                                 {#{dyn.best} t n ≡
                                  (match n motive (λ _ → Bool)
                                    | 0 => false
                                    | suc j => #{dyn.any} t j) : Bool} :=
      λ (+ t : State) → λ (+ n : Nat) → refl

    def class-one-eq : evidence Π (+ t : State) → Π (+ b : Action) → Π (+ n : Nat) →
                                {#{dyn.one} t b n ≡
                                 (match (#{dyn.pos} (snd (step t b))) motive (λ _ → Bool)
                                   | true => true
                                   | false => #{dyn.best} (fst (step t b)) n) : Bool} :=
      λ (+ t : State) → λ (+ b : Action) → λ (+ n : Nat) → refl

    def class-any-eq : evidence Π (+ t : State) → Π (+ n : Nat) →
                                {#{dyn.any} t n ≡
                                 hit-fold (λ (+ b : Action) → #{dyn.one} t b n) all-actions : Bool} :=
      λ (+ t : State) → λ (+ n : Nat) → refl
    """
  end

  defp reach_defs(actions, dyn) do
    arms =
      Enum.map_join(actions, "\n", fn action ->
        "      | #{action} => #{dyn.one} s #{action} horizon"
      end)

    eqs =
      Enum.map_join(actions, "\n", fn action ->
        "      | #{action} => #{bridge(dyn, "s", action)}"
      end)

    """
    def class-reach : run Π (+ s : State) → Π (+ a : Action) → Bool :=
      λ (+ s : State) → λ (+ a : Action) →
        match a motive (λ _ → Bool)
    #{arms}

    def class-reach-eq : evidence Π (+ s : State) → Π (+ a : Action) →
                                  {class-reach s a ≡ hit s a horizon : Bool} :=
      λ (+ s : State) → λ (+ a : Action) →
        match a motive (λ x → {class-reach s x ≡ hit s x horizon : Bool})
    #{eqs}
    """
  end

  defp conflict_def(dyn) do
    """
    def class-atom-conflict : evidence Π (+ s : State) → Π (+ a : Action) →
                                       Π (hp : {#{dyn.pos} (snd (step s a)) ≡ true : Bool}) →
                                       Π (hn : {#{dyn.one} s a horizon ≡ false : Bool}) →
                                       Empty :=
      λ (+ s : State) → λ (+ a : Action) →
      λ (hp : {#{dyn.pos} (snd (step s a)) ≡ true : Bool}) →
      λ (hn : {#{dyn.one} s a horizon ≡ false : Bool}) →
        reach-conflict s a
          (rewrite (sym Bool (#{dyn.pos} (snd (step s a))) (class-pos (snd (step s a)))
                     (class-pos-eq (snd (step s a))))
            motive (λ z → {z ≡ true : Bool})
          in hp)
          (rewrite (sym Bool (#{dyn.one} s a horizon) (hit s a horizon) (#{bridge(dyn, "s", "a")}))
            motive (λ z → {z ≡ false : Bool})
          in hn)
    """
  end

  defp bridge(dyn, state, action) do
    "rec-is-hit horizon #{dyn.pos} #{dyn.one} #{dyn.best} #{dyn.any} class-pos-eq class-best-eq class-one-eq class-any-eq #{state} #{action}"
  end

  defp arm_eqs(arms, bound, ctx) do
    Enum.map_join(Enum.with_index(arms), "\n", fn {arm, index} ->
      decl = Map.fetch!(bound.decl, arm.name)
      formula = term(arm.pred, ctx)

      """
      def class-arm-eq-#{index} : evidence Π (+ s : State) →
                                         {#{bound.names.eval} #{decl} s ≡ #{formula} : Bool} :=
        λ (+ s : State) → refl
      """
    end)
  end

  defp rank_def(bound, arms, actions) do
    """
    def rank : spec Π (s : State) → Π (a : Action) → Π (b : Action) → Type :=
      λ (s : State) → λ (a : Action) → λ (b : Action) →
        #{Cert.cascade(bound, arms, actions)}
    """
  end

  # The apply motive names these suffixes. Inlining the action match
  # there makes the checker compare one copy of the ranking per branch.
  defp named_ranks(arms, bound, actions) do
    prefs =
      Enum.map_join(actions, "\n", fn action ->
        """
        def class-pref-#{action} : spec Π (y : Action) → Π (z : Action) → Type :=
          λ (y : Action) → λ (z : Action) →
            #{Cert.preference(actions, action, "y", "z")}
        """
      end)

    ranks =
      arms
      |> Enum.with_index()
      |> Enum.reverse()
      |> Enum.map_join("\n", fn {arm, index} ->
        ev = "#{bound.names.eval} #{Map.fetch!(bound.decl, arm.name)} s"
        rest = Enum.drop(arms, index + 1)

        false_ty =
          if rest == [] do
            "class-pref-#{arm.else} a b"
          else
            "class-rank-#{index + 1} s a b"
          end

        """
        def class-rank-#{index} : spec Π (s : State) → Π (a : Action) → Π (b : Action) → Type :=
          λ (s : State) → λ (a : Action) → λ (b : Action) →
            (match #{ev} motive (λ _ → Type)
              | true => class-pref-#{arm.action} a b
              | false => #{false_ty})
        """
      end)

    prefs <> "\n" <> ranks
  end

  defp win_defs(arms, _actions, bound, ctx) do
    yes =
      Enum.map_join(Enum.with_index(arms), "\n", fn {arm, index} ->
        win_def(index, arm.action, arms, bound, ctx)
      end)

    no = else_def(List.last(arms).else, arms, bound, ctx)
    yes <> "\n" <> no
  end

  defp win_def(index, winner, arms, bound, ctx) do
    params = win_params(index, arms, bound)
    goal = goal("a", winner)

    body =
      table(ctx.atoms, %{
        ctx
        | bits: %{},
          index: index,
          winner: winner,
          goal: goal,
          eq_true: "e#{index}",
          eq_false: Enum.map(0..(index - 1)//1, &"e#{&1}")
      })

    """
    def class-win-#{index} : evidence Π (+ s : State) → Π (+ a : Action) →
    #{param_types(params)}
                                    #{goal} :=
      λ (+ s : State) → λ (+ a : Action) →
    #{param_lams(params)}
        #{body}
    """
  end

  defp else_def(winner, arms, bound, ctx) do
    params =
      Enum.map(Enum.with_index(arms), fn {arm, index} ->
        {"e#{index}", eval_eq(bound, arm, false)}
      end)

    goal = goal("a", winner)

    body =
      table(ctx.atoms, %{
        ctx
        | bits: %{},
          index: :else,
          winner: winner,
          goal: goal,
          eq_true: nil,
          eq_false: Enum.map(0..(length(arms) - 1)//1, &"e#{&1}")
      })

    """
    def class-win-else : evidence Π (+ s : State) → Π (+ a : Action) →
    #{param_types(params)}
                                  #{goal} :=
      λ (+ s : State) → λ (+ a : Action) →
    #{param_lams(params)}
        #{body}
    """
  end

  defp win_params(index, arms, bound) do
    prior =
      Enum.map(0..(index - 1)//1, fn j ->
        {"e#{j}", eval_eq(bound, Enum.at(arms, j), false)}
      end)

    [{"e#{index}", eval_eq(bound, Enum.at(arms, index), true)} | prior]
  end

  defp eval_eq(bound, arm, bit) do
    decl = Map.fetch!(bound.decl, arm.name)
    word = if bit, do: "true", else: "false"
    "{#{bound.names.eval} #{decl} s ≡ #{word} : Bool}"
  end

  defp param_types(params) do
    Enum.map_join(params, "\n", fn {name, type} ->
      "                              Π (#{name} : #{type}) →"
    end)
  end

  defp param_lams(params) do
    Enum.map_join(params, "\n", fn {name, type} ->
      "      λ (#{name} : #{type}) →"
    end)
  end

  defp apply_def(arms, bound, actions) do
    """
    def class-apply : evidence Π (+ s : State) → Π (+ a : Action) → Π (+ b : Action) →
                               Π (r : rank s a b) →
                               Dom Reward le (action-value s a) (action-value s b) :=
      λ (+ s : State) → λ (+ a : Action) → λ (+ b : Action) → λ (r : rank s a b) →
        #{cascade(arms, bound, actions, "r", 0, [])}
    """
  end

  defp cascade([arm | rest], bound, actions, proof, index, prior) do
    ev = eval_app(bound, arm)
    ename = "e#{index}"
    dom = goal("a", "b")
    true_ty = "class-pref-#{arm.action} a b"

    false_ty =
      if rest == [] do
        "class-pref-#{arm.else} a b"
      else
        "class-rank-#{index + 1} s a b"
      end

    win = fn left ->
      args = Enum.join([ename | prior], " ")
      "class-win-#{index} s #{left} #{args}"
    end

    false_body =
      if rest == [] do
        args = Enum.join(prior ++ [ename], " ")

        else_call = fn left ->
          "class-win-else s #{left} #{args}"
        end

        "#{split(actions, arm.else, else_call)} q"
      else
        cascade(rest, bound, actions, "q", index + 1, prior ++ [ename])
      end

    inner = """
    (match bit motive (λ _ → Type)
      | true => #{true_ty}
      | false => #{false_ty})
    """

    """
    (match #{ev} motive (λ bit → {#{ev} ≡ bit : Bool} → Π (q : #{String.trim(inner)}) → #{dom})
      | true => λ (#{ename} : {#{ev} ≡ true : Bool}) → λ (q : #{true_ty}) →
          #{split(actions, arm.action, win)} q
      | false => λ (#{ename} : {#{ev} ≡ false : Bool}) → λ (q : #{false_ty}) →
          #{false_body})
    refl
    #{proof}
    """
    |> String.trim()
  end

  defp eval_app(bound, arm) do
    "#{bound.names.eval} #{Map.fetch!(bound.decl, arm.name)} s"
  end

  defp split(actions, winner, call) do
    pref = "class-pref-#{winner} y b"

    branches =
      Enum.map_join(actions, "\n", fn left ->
        "| #{left} => #{b_match(actions, left, winner, call)}"
      end)

    """
    (match a motive (λ y → Π (r : #{pref}) → #{goal("y", "b")})
      #{branches})
    """
    |> String.trim()
  end

  defp b_match(actions, left, winner, call) do
    cells = "class-pref-#{winner} #{left} z"

    branches =
      Enum.map_join(actions, "\n", fn right ->
        "| #{right} => #{split_leaf(left, right, winner, call)}"
      end)

    """
    (match b motive (λ z → Π (r : #{cells}) → #{goal(left, "z")})
      #{branches})
    """
    |> String.trim()
  end

  defp split_leaf(left, right, winner, call) do
    cond do
      left == right ->
        "λ (u : Unit) → class-same s #{left}"

      right == winner ->
        "λ (u : Unit) → #{call.(left)}"

      true ->
        "λ (r : Empty) → matchEmpty r motive (λ _ → #{goal(left, right)})"
    end
  end

  defp preserves_def do
    """
    def preserves : evidence CoindHomo rank :=
      λ (a : Action) → λ (b : Action) → λ (s : State) → λ (r : rank s a b) →
        class-apply s a b r
    """
  end

  # Split an atom only when the two sides are different cases. The
  # winner's reach bit comes first, so one true branch covers every
  # row in which that action reaches. The table stays linear in the
  # atoms instead of exponential in them.
  defp table(atoms, ctx), do: table_split(prefer_winner(atoms, ctx), ctx)

  defp prefer_winner(atoms, ctx) do
    winner = {:reach, ctx.winner}
    {hit, rest} = Enum.split_with(atoms, &(&1 == winner))
    hit ++ rest
  end

  defp table_split([], ctx), do: leaf(ctx)

  defp table_split([atom | rest] = atoms, ctx) do
    if prune?(atoms, ctx) do
      leaf(ctx)
    else
      term = atom_term(atom, ctx)
      hyp = Map.fetch!(ctx.hyps, atom)

      """
      (match #{term} motive (λ b → {#{term} ≡ b : Bool} → #{ctx.goal})
        | true => λ (#{hyp} : {#{term} ≡ true : Bool}) →
            #{table(rest, put_bit(ctx, atom, true))}
        | false => λ (#{hyp} : {#{term} ≡ false : Bool}) →
            #{table(rest, put_bit(ctx, atom, false))})
      refl
      """
      |> String.trim()
    end
  end

  defp prune?(rest, ctx) do
    case one_class(rest, ctx) do
      {:ok, class} -> ready?(class, ctx)
      :no -> false
    end
  end

  defp one_class(rest, ctx) do
    rest
    |> completions()
    |> Enum.reduce_while(:empty, fn extra, acc ->
      class =
        classify(Map.merge(ctx.bits, extra), ctx.actions, ctx.arms, ctx.index, ctx.winner)

      cond do
        class == :bad -> {:halt, :bad}
        acc in [:empty, class] -> {:cont, class}
        true -> {:halt, :mixed}
      end
    end)
    |> case do
      class when class in [:win, :tie, :conflict, :mismatch] -> {:ok, class}
      _ -> :no
    end
  end

  defp completions([]), do: [%{}]

  defp completions([atom | rest]) do
    Enum.flat_map(completions(rest), fn base ->
      [Map.put(base, atom, false), Map.put(base, atom, true)]
    end)
  end

  defp ready?(:win, ctx), do: Map.get(ctx.bits, {:reach, ctx.winner}) == true

  defp ready?(:tie, ctx) do
    Enum.all?(ctx.actions, &(Map.get(ctx.bits, {:reach, &1}) == false))
  end

  defp ready?(:conflict, ctx) do
    case conflict_action(ctx.bits, ctx.actions) do
      nil ->
        false

      action ->
        Map.has_key?(ctx.hyps, {:pos, action}) and Map.has_key?(ctx.hyps, {:reach, action})
    end
  end

  defp ready?(:mismatch, ctx), do: mismatch_closed?(ctx)
  defp ready?(:bad, _ctx), do: false

  # The leaf reads the all-false completion of whatever was not split.
  # Prune only when that completion's proof does not need a later bit.
  defp mismatch_closed?(ctx) do
    case gap_of(ctx) do
      {:ok, pred} -> match?({:ok, _}, formula_closed?(pred, ctx))
      :no -> false
    end
  end

  defp gap_of(ctx) do
    found =
      Enum.find_value(Enum.with_index(ctx.arms), fn {arm, j} ->
        case holds_closed(arm.pred, ctx) do
          :missing ->
            :missing

          {:ok, bit} ->
            cond do
              ctx.index == :else and bit -> {:ok, arm.pred}
              is_integer(ctx.index) and j < ctx.index and bit -> {:ok, arm.pred}
              ctx.index == j and not bit -> {:ok, arm.pred}
              true -> nil
            end
        end
      end)

    case found do
      {:ok, pred} -> {:ok, pred}
      _ -> :no
    end
  end

  defp holds_closed({:not, pred}, ctx) do
    case holds_closed(pred, ctx) do
      {:ok, bit} -> {:ok, not bit}
      :missing -> :missing
    end
  end

  defp holds_closed({:and, left, right}, ctx) do
    case holds_closed(left, ctx) do
      :missing -> :missing
      {:ok, false} -> {:ok, false}
      {:ok, true} -> holds_closed(right, ctx)
    end
  end

  defp holds_closed({:or, left, right}, ctx) do
    case holds_closed(left, ctx) do
      :missing -> :missing
      {:ok, true} -> {:ok, true}
      {:ok, false} -> holds_closed(right, ctx)
    end
  end

  defp holds_closed({:feat, name}, ctx), do: fetch_bit(ctx, feat_atom(name, ctx.actions))

  defp holds_closed({:self, stem, action, _}, ctx), do: fetch_bit(ctx, stem_atom(stem, action))

  defp holds_closed({:other, stem, action, _}, ctx) do
    ctx.actions
    |> Enum.reject(&(&1 == action))
    |> other_closed(stem, ctx)
  end

  defp holds_closed(_pred, _ctx), do: :missing

  defp other_closed([], _stem, _ctx), do: {:ok, false}

  defp other_closed([action | rest], stem, ctx) do
    case Map.fetch(ctx.bits, stem_atom(stem, action)) do
      :error -> :missing
      {:ok, true} -> {:ok, true}
      {:ok, false} -> other_closed(rest, stem, ctx)
    end
  end

  defp formula_closed?({:not, pred}, ctx) do
    case formula_closed?(pred, ctx) do
      {:ok, bit} -> {:ok, not bit}
      :missing -> :missing
    end
  end

  defp formula_closed?({:and, left, right}, ctx) do
    case formula_closed?(left, ctx) do
      :missing -> :missing
      {:ok, false} -> {:ok, false}
      {:ok, true} -> formula_closed?(right, ctx)
    end
  end

  defp formula_closed?({:or, left, right}, ctx) do
    case formula_closed?(left, ctx) do
      :missing -> :missing
      {:ok, true} -> {:ok, true}
      {:ok, false} -> formula_closed?(right, ctx)
    end
  end

  defp formula_closed?({:feat, name}, ctx), do: fetch_bit(ctx, feat_atom(name, ctx.actions))

  defp formula_closed?({:self, stem, action, _}, ctx), do: fetch_bit(ctx, stem_atom(stem, action))

  defp formula_closed?({:other, stem, action, _}, ctx) do
    ctx.actions
    |> Enum.reject(&(&1 == action))
    |> other_closed(stem, ctx)
  end

  defp formula_closed?(_pred, _ctx), do: :missing

  defp fetch_bit(ctx, atom) do
    case Map.fetch(ctx.bits, atom) do
      {:ok, bit} -> {:ok, bit}
      :error -> :missing
    end
  end

  defp put_bit(ctx, atom, bit), do: %{ctx | bits: Map.put(ctx.bits, atom, bit)}

  defp leaf(ctx) do
    case classify(ctx.bits, ctx.actions, ctx.arms, ctx.index, ctx.winner) do
      :conflict ->
        conflict_leaf(conflict_action(ctx.bits, ctx.actions), ctx)

      :win ->
        win_leaf(ctx)

      :tie ->
        tie_leaf(ctx)

      :mismatch ->
        mismatch_leaf(ctx)

      :bad ->
        raise "class proof: a bad row survived the scan"
    end
  end

  defp win_leaf(ctx) do
    hyp = Map.fetch!(ctx.hyps, {:reach, ctx.winner})

    """
    class-from-true s #{ctx.winner} a
      (λ (+ b : Action) → class-reach s b)
      (λ (+ b : Action) → class-reach-eq s b)
      #{hyp}
    """
    |> String.trim()
  end

  defp tie_leaf(ctx) do
    "class-from-miss s a #{ctx.winner} (#{tie_proof(ctx)})"
  end

  defp tie_proof(ctx) do
    ask = "(class-hit-ask s)"

    chain =
      Enum.reduce(Enum.reverse(ctx.actions), "fold-nil-eq #{ask}", fn action, acc ->
        rest = Enum.drop(ctx.actions, Enum.find_index(ctx.actions, &(&1 == action)) + 1)

        "class-cons-false #{ask} #{action} #{list_term(rest)} (#{reach_false(action, ctx)}) (#{acc})"
      end)

    """
    rewrite (any-fold s horizon)
      motive (λ z → {z ≡ false : Bool})
    in
      #{chain}
    """
    |> String.trim()
  end

  # The equation from rec-is-hit is {dyn-one ≡ hit}. sym flips it, so the
  # hypothesis is checked on the dyn-one side and the result is the hit
  # side. The other direction makes the checker unfold both runs at the
  # horizon, one action list per successor.
  defp reach_false(action, ctx) do
    hyp = Map.fetch!(ctx.hyps, {:reach, action})
    one = "#{ctx.one} s #{action} horizon"

    """
    rewrite (sym Bool (#{one}) (hit s #{action} horizon) (#{bridge_ctx(ctx, "s", action)}))
      motive (λ z → {z ≡ false : Bool})
    in #{hyp}
    """
    |> String.trim()
  end

  defp bridge_ctx(ctx, state, action) do
    bridge(%{pos: ctx.pos, one: ctx.one, best: ctx.best, any: ctx.any}, state, action)
  end

  defp conflict_leaf(action, ctx) do
    hp = Map.fetch!(ctx.hyps, {:pos, action})
    hn = Map.fetch!(ctx.hyps, {:reach, action})
    "matchEmpty (class-atom-conflict s #{action} #{hp} #{hn}) motive (λ _ → #{ctx.goal})"
  end

  defp mismatch_leaf(ctx) do
    case first_gap(ctx) do
      :current ->
        {bit, proof} = prove(Enum.at(ctx.arms, ctx.index).pred, ctx)
        if bit, do: raise("class proof: the deciding arm holds on a mismatch row")
        contra_true(ctx, ctx.index, proof)

      {:earlier, j} ->
        {bit, proof} = prove(Enum.at(ctx.arms, j).pred, ctx)
        unless bit, do: raise("class proof: an earlier arm fails on a mismatch row")
        contra_false(ctx, j, proof)
    end
  end

  defp contra_true(ctx, index, proof) do
    ev = eval_term(ctx, index)

    """
    matchEmpty
      (class-ft
        (rewrite (sym Bool #{ev} false
                   (rewrite (class-arm-eq-#{index} s)
                      motive (λ z → {z ≡ false : Bool})
                    in #{paren(proof)}))
           motive (λ z → {z ≡ true : Bool})
         in #{ctx.eq_true}))
      motive (λ _ → #{ctx.goal})
    """
    |> String.trim()
  end

  defp contra_false(ctx, index, proof) do
    ev = eval_term(ctx, index)
    ef = Enum.at(ctx.eq_false, index)

    """
    matchEmpty
      (class-ft
        (rewrite (sym Bool #{ev} false #{ef})
           motive (λ z → {z ≡ true : Bool})
         in
           (rewrite (class-arm-eq-#{index} s)
              motive (λ z → {z ≡ true : Bool})
            in #{paren(proof)})))
      motive (λ _ → #{ctx.goal})
    """
    |> String.trim()
  end

  defp eval_term(ctx, index) do
    "(#{eval_app(ctx.bound, Enum.at(ctx.arms, index))})"
  end

  defp first_gap(ctx) do
    Enum.find_value(Enum.with_index(ctx.arms), fn {arm, j} ->
      bit = holds?(arm.pred, ctx.bits, ctx.actions)

      cond do
        ctx.index == :else and bit -> {:earlier, j}
        is_integer(ctx.index) and j < ctx.index and bit -> {:earlier, j}
        ctx.index == j and not bit -> :current
        true -> nil
      end
    end)
  end

  defp goal(left, right), do: "Dom Reward le (action-value s #{left}) (action-value s #{right})"

  defp hyps(atoms) do
    Map.new(Enum.with_index(atoms), fn {atom, index} -> {atom, "ha#{index}"} end)
  end

  defp family_pred?(true, _), do: false
  defp family_pred?(false, _), do: false
  defp family_pred?({:feat, name}, actions), do: feat_atom(name, actions) != :no
  defp family_pred?({:self, stem, action, _}, actions), do: stem in @stems and action in actions
  defp family_pred?({:other, stem, action, _}, actions), do: stem in @stems and action in actions
  defp family_pred?({:not, pred}, actions), do: family_pred?(pred, actions)

  defp family_pred?({:and, left, right}, actions) do
    family_pred?(left, actions) and family_pred?(right, actions)
  end

  defp family_pred?({:or, left, right}, actions) do
    family_pred?(left, actions) and family_pred?(right, actions)
  end

  defp family_pred?(_, _), do: false

  defp atoms_of(actions, arms) do
    pos =
      arms
      |> Enum.flat_map(&pos_actions(&1.pred, actions))
      |> Enum.uniq()

    Enum.map(actions, &{:reach, &1}) ++ Enum.map(Enum.filter(actions, &(&1 in pos)), &{:pos, &1})
  end

  defp pos_actions({:feat, name}, actions) do
    case feat_atom(name, actions) do
      {:pos, action} -> [action]
      _ -> []
    end
  end

  defp pos_actions({:self, "has-pos-reward", action, _}, actions) do
    if action in actions, do: [action], else: []
  end

  defp pos_actions({:other, "has-pos-reward", action, _}, actions) do
    Enum.reject(actions, &(&1 == action))
  end

  defp pos_actions({:not, pred}, actions), do: pos_actions(pred, actions)

  defp pos_actions({:and, left, right}, actions),
    do: pos_actions(left, actions) ++ pos_actions(right, actions)

  defp pos_actions({:or, left, right}, actions),
    do: pos_actions(left, actions) ++ pos_actions(right, actions)

  defp pos_actions(_, _), do: []

  defp feat_atom(name, actions) do
    cond do
      String.starts_with?(name, "reaches-pos-") ->
        action = String.replace_prefix(name, "reaches-pos-", "")
        if action in actions, do: {:reach, action}, else: :no

      String.starts_with?(name, "has-pos-reward-") ->
        action = String.replace_prefix(name, "has-pos-reward-", "")
        if action in actions, do: {:pos, action}, else: :no

      true ->
        :no
    end
  end

  defp stem_atom("reaches-pos", action), do: {:reach, action}
  defp stem_atom("has-pos-reward", action), do: {:pos, action}

  defp bad?(actions, arms, atoms) do
    last = Integer.pow(2, length(atoms)) - 1
    branches = Enum.map(0..(length(arms) - 1)//1, &{:arm, &1}) ++ [:else]

    Enum.any?(0..last, fn row ->
      bits = row_bits(atoms, row)

      Enum.any?(branches, fn branch ->
        {index, winner} = branch_of(branch, arms)
        classify(bits, actions, arms, index, winner) == :bad
      end)
    end)
  end

  defp branch_of({:arm, index}, arms), do: {index, Enum.at(arms, index).action}
  defp branch_of(:else, arms), do: {:else, List.last(arms).else}

  defp row_bits(atoms, row) do
    Map.new(Enum.with_index(atoms), fn {atom, index} ->
      {atom, rem(div(row, Integer.pow(2, index)), 2) == 1}
    end)
  end

  defp classify(bits, actions, arms, index, winner) do
    cond do
      conflict_action(bits, actions) -> :conflict
      Map.get(bits, {:reach, winner}, false) -> :win
      Enum.all?(actions, &(not Map.get(bits, {:reach, &1}, false))) -> :tie
      matching?(bits, actions, arms, index) -> :bad
      true -> :mismatch
    end
  end

  defp conflict_action(bits, actions) do
    Enum.find(actions, fn action ->
      Map.get(bits, {:pos, action}, false) and not Map.get(bits, {:reach, action}, false)
    end)
  end

  defp matching?(bits, actions, arms, index) do
    Enum.all?(Enum.with_index(arms), fn {arm, j} ->
      bit = holds?(arm.pred, bits, actions)

      cond do
        index == :else -> not bit
        j < index -> not bit
        j == index -> bit
        true -> true
      end
    end)
  end

  defp holds?(pred, bits, actions) do
    case pred do
      {:not, inner} ->
        not holds?(inner, bits, actions)

      {:and, left, right} ->
        holds?(left, bits, actions) and holds?(right, bits, actions)

      {:or, left, right} ->
        holds?(left, bits, actions) or holds?(right, bits, actions)

      {:feat, name} ->
        Map.fetch!(bits, feat_atom(name, actions))

      {:self, stem, action, _} ->
        Map.fetch!(bits, stem_atom(stem, action))

      {:other, stem, action, _} ->
        actions
        |> Enum.reject(&(&1 == action))
        |> Enum.any?(fn other -> Map.fetch!(bits, stem_atom(stem, other)) end)
    end
  end

  defp term({:not, pred}, ctx), do: "(#{ctx.notb} #{paren(term(pred, ctx))})"

  defp term({:and, left, right}, ctx),
    do: "(#{ctx.andb} #{paren(term(left, ctx))} #{paren(term(right, ctx))})"

  defp term({:or, left, right}, ctx),
    do: "(#{ctx.orb} #{paren(term(left, ctx))} #{paren(term(right, ctx))})"

  defp term({:feat, name}, ctx), do: atom_term(feat_atom(name, ctx.actions), ctx)
  defp term({:self, stem, action, _}, ctx), do: atom_term(stem_atom(stem, action), ctx)

  defp term({:other, stem, action, _}, ctx) do
    ctx.actions
    |> Enum.reject(&(&1 == action))
    |> Enum.map(&atom_term(stem_atom(stem, &1), ctx))
    |> or_term(ctx.orb)
  end

  defp or_term([], _orb), do: "false"
  defp or_term([one], _orb), do: one
  defp or_term([one | rest], orb), do: "(#{orb} #{paren(one)} #{paren(or_term(rest, orb))})"

  defp atom_term({:reach, action}, ctx), do: "(#{ctx.one} s #{action} horizon)"
  defp atom_term({:pos, action}, ctx), do: "(#{ctx.pos} (snd (step s #{action})))"

  defp prove({:not, pred}, ctx) do
    {bit, proof} = prove(pred, ctx)
    lemma = if bit, do: ctx.lnf, else: ctx.lnt
    {not bit, call(lemma, [term(pred, ctx), proof])}
  end

  defp prove({:and, left, right}, ctx) do
    {lb, lp} = prove(left, ctx)

    if lb do
      {rb, rp} = prove(right, ctx)
      {rb, call(ctx.lat, [term(left, ctx), term(right, ctx), bool_word(rb), lp, rp])}
    else
      {false, call(ctx.laf, [term(left, ctx), term(right, ctx), lp])}
    end
  end

  defp prove({:or, left, right}, ctx) do
    {lb, lp} = prove(left, ctx)

    if lb do
      {true, call(ctx.lor, [term(left, ctx), term(right, ctx), lp])}
    else
      {rb, rp} = prove(right, ctx)
      {rb, call(ctx.lof, [term(left, ctx), term(right, ctx), bool_word(rb), lp, rp])}
    end
  end

  defp prove({:feat, name}, ctx) do
    atom = feat_atom(name, ctx.actions)
    {Map.fetch!(ctx.bits, atom), Map.fetch!(ctx.hyps, atom)}
  end

  defp prove({:self, stem, action, _}, ctx) do
    atom = stem_atom(stem, action)
    {Map.fetch!(ctx.bits, atom), Map.fetch!(ctx.hyps, atom)}
  end

  defp prove({:other, stem, action, _}, ctx) do
    ctx.actions
    |> Enum.reject(&(&1 == action))
    |> prove_others(stem, ctx)
  end

  # A true disjunct does not read the bits after it. Those rows are one case.
  # One remaining action is that action, the same term `or_term` prints.
  # Wrapping it as `orb atom false` does not convert with the formula.
  defp prove_others([], _stem, _ctx), do: {false, "refl"}

  defp prove_others([action], stem, ctx) do
    atom = stem_atom(stem, action)
    {Map.fetch!(ctx.bits, atom), Map.fetch!(ctx.hyps, atom)}
  end

  defp prove_others([action | rest], stem, ctx) do
    atom = stem_atom(stem, action)
    bit = Map.fetch!(ctx.bits, atom)
    proof = Map.fetch!(ctx.hyps, atom)
    t = atom_term(atom, ctx)
    rt = or_term(Enum.map(rest, &atom_term(stem_atom(stem, &1), ctx)), ctx.orb)

    if bit do
      {true, call(ctx.lor, [t, rt, proof])}
    else
      {rb, rp} = prove_others(rest, stem, ctx)
      {rb, call(ctx.lof, [t, rt, bool_word(rb), proof, rp])}
    end
  end

  defp call(fun, args), do: Enum.join([fun | Enum.map(args, &paren/1)], " ")

  defp paren(term) do
    cond do
      term in ["true", "false", "refl", "horizon"] -> term
      String.match?(term, ~r/^[A-Za-z_][A-Za-z0-9_\-]*$/) -> term
      String.starts_with?(term, "(") -> term
      true -> "(#{term})"
    end
  end

  defp bool_word(true), do: "true"
  defp bool_word(false), do: "false"
end
