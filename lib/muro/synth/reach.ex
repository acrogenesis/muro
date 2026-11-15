defmodule Muro.Synth.Reach do
  @moduledoc """
  The reachability runs in a policy book.

  `dyn-best-pos s k` is false at horizon 0, and otherwise the best
  action from `s` pays a positive reward inside `k` steps.
  `dyn-one` is one action. `dyn-any` is some action. `reaches-pos`
  reads `dyn-one` at the environment's horizon.

  When the cover is finite, closed under `step`, and `cover_match`
  can split it, the book tabulates `dyn-best-pos` for every cover
  state and every horizon up to the environment's. The table is a
  match in the book. The checker does not trust the fill.

  Soundness inside the table is an inductive family of `refl`s.
  `dyn-best-pos s 0` agrees with `false`. `dyn-best-pos s (j + 1)`
  agrees with one step of `dyn-any s j`, and that step reads the
  table at horizon `j`. The chain ends at the zero arm. A wrong cell
  fails at the first horizon where it disagrees with that step. The
  table is not shown to be sound by comparing it, in one shot, with
  the recurrence unfolded out to the horizon.

  Horizons past the table, and a state the match does not hit, call
  the same recurrence as a separate block: `dyn-best-rec`,
  `dyn-one-rec`, and `dyn-any-rec`. That block is only the fallback.
  It does not call the table. The table's fallback calls it, which
  is legal because the call is not inside the block. Above the
  horizon, and off the cover, the runs are the recurrence itself,
  not a second table.

  The agreement term is a balanced tree, in chunks of `@chunk`
  cells, so the match depth stays inside the checker's fuel. A cover
  that is not closed, that the match cannot split, or that is larger
  than `@domain_cap` states, keeps the three recursive runs and
  emits no table. The search's own memo of the same recursion is not
  this table, and the checker never reads it.
  """

  alias Muro.Synth.Book
  alias Muro.Synth.Term

  @chunk 1024
  @domain_cap 100_000

  @doc """
  The reachability text, and the names it reserved.

  `best`, `one`, and `any` are the runs `eval` calls.
  """
  def sources(host, best, one, any, pos, taken) do
    actions = actions_of(host)
    states = cover(host)

    if tabulate?(host, states, actions) do
      case prepare(host, states) do
        :recur ->
          {recursive(best, one, any, pos, actions), taken}

        {:ok, bits} ->
          tabulated(host, states, bits, best, one, any, pos, actions, taken)
      end
    else
      {recursive(best, one, any, pos, actions), taken}
    end
  end

  defp tabulated(host, states, bits, best, one, any, pos, actions, taken) do
    saved = taken
    {known, taken} = Book.reserve("dyn-known", taken)
    {best_rec, taken} = Book.reserve("dyn-best-rec", taken)
    {one_rec, taken} = Book.reserve("dyn-one-rec", taken)
    {any_rec, taken} = Book.reserve("dyn-any-rec", taken)

    case known_match(host, states, bits, any_rec) do
      :open ->
        {recursive(best, one, any, pos, actions), saved}

      {:ok, known_text} ->
        {evidence, taken} = evidence(host, states, best, any, taken)

        text =
          Enum.join(
            [
              recursive(best_rec, one_rec, any_rec, pos, actions),
              front(best, known, one, any, pos, actions, known_text),
              evidence
            ],
            "\n"
          )

        {text, taken}
    end
  end

  defp known_match(host, states, bits, any_rec) do
    by_spell = Map.new(states, fn state -> {Term.spell(state), bits_of(bits, state)} end)

    body_of = fn spell ->
      horizon_body(any_rec, paren(spell), Map.fetch!(by_spell, spell), host.horizon)
    end

    miss = fn src -> "#{any_rec} #{paren(src)} j" end

    Term.cover_match(host.schema, "s", states, fn _src -> "Bool" end, body_of, miss)
  end

  # `bits` is `best_pos` at horizons 1..horizon. The last `suc` is
  # every larger horizon, and it calls the recurrence.
  defp horizon_body(any_rec, spell, [], _horizon) do
    "#{any_rec} #{spell} j"
  end

  defp horizon_body(any_rec, spell, bits, horizon) do
    nest(any_rec, spell, bits, horizon, "j", 0)
  end

  defp nest(any_rec, spell, [bit], horizon, var, index) do
    nxt = "rk#{index}"

    """
    (match #{var} motive (λ _ → Bool)
      | 0 => #{word(bit)}
      | suc #{nxt} => #{any_rec} #{spell} #{paren(apply_sucs(nxt, horizon))})
    """
  end

  defp nest(any_rec, spell, [bit | rest], horizon, var, index) do
    nxt = "rk#{index}"

    """
    (match #{var} motive (λ _ → Bool)
      | 0 => #{word(bit)}
      | suc #{nxt} => #{nest(any_rec, spell, rest, horizon, nxt, index + 1)})
    """
  end

  defp apply_sucs(var, 0), do: var
  defp apply_sucs(var, 1), do: "suc #{var}"
  defp apply_sucs(var, n) when n > 1, do: "suc (" <> apply_sucs(var, n - 1) <> ")"

  defp front(best, known, one, any, pos, actions, known_text) do
    """
    def #{best} : run Π (+ s : State) → Π (+ k : Nat) → Bool :=
      λ (+ s : State) → λ (+ k : Nat) →
        match k motive (λ _ → Bool)
          | 0 => false
          | suc j => #{known} s j

    def #{known} : run Π (+ s : State) → Π (+ j : Nat) → Bool :=
      λ (+ s : State) → λ (+ j : Nat) →
        #{known_text}

    def #{one} : run Π (+ s : State) → Π (+ a : Action) → Π (+ k : Nat) → Bool :=
      λ (+ s : State) → λ (+ a : Action) → λ (+ k : Nat) →
        (match (#{pos} (snd (step s a))) motive (λ _ → Bool)
          | true => true
          | false => #{best} (fst (step s a)) k)

    def #{any} : run Π (+ s : State) → Π (+ j : Nat) → Bool :=
      λ (+ s : State) → λ (+ j : Nat) →
        #{any_body(one, actions)}
    """
  end

  # The block descends on the horizon. `best` is first. `one` passes
  # that same horizon to it. `any` passes its horizon to `one`. The
  # call from `suc j` is the smaller argument, and `any` is later in
  # the block.
  defp recursive(best, one, any, pos, actions) do
    """
    def #{best} : run Π (+ s : State) → Π (+ k : Nat) → Bool :=
      λ (+ s : State) → λ (+ k : Nat) →
        match k motive (λ _ → Bool)
          | 0 => false
          | suc j => #{any} s j

    def #{one} : run Π (+ s : State) → Π (+ a : Action) → Π (+ k : Nat) → Bool :=
      λ (+ s : State) → λ (+ a : Action) → λ (+ k : Nat) →
        (match (#{pos} (snd (step s a))) motive (λ _ → Bool)
          | true => true
          | false => #{best} (fst (step s a)) k)

    def #{any} : run Π (+ s : State) → Π (+ j : Nat) → Bool :=
      λ (+ s : State) → λ (+ j : Nat) →
        #{any_body(one, actions)}
    """
  end

  defp any_body(one, [action]) do
    "#{one} s #{action} j"
  end

  defp any_body(one, [action | rest]) do
    """
    (match (#{one} s #{action} j) motive (λ _ → Bool)
      | true => true
      | false => #{any_body(one, rest)})
    """
  end

  defp evidence(host, states, best, any, taken) do
    horizon = host.horizon

    cells =
      Enum.flat_map(states, fn state ->
        spell = paren(Term.spell(state))
        [eq_false(best, spell) | eq_steps(best, any, spell, horizon)]
      end)

    {blocks, taken} =
      cells
      |> Enum.chunk_every(@chunk)
      |> Enum.map_reduce(taken, fn chunk, taken ->
        {agrees, taken} = Book.reserve("dyn-reach-agrees", taken)
        {holds, taken} = Book.reserve("dyn-reach-holds", taken)
        {agree_block(agrees, holds, band(chunk)), taken}
      end)

    {Enum.join(blocks, "\n"), taken}
  end

  defp eq_steps(_best, _any, _spell, horizon) when horizon <= 0, do: []

  defp eq_steps(best, any, spell, horizon) do
    Enum.map(0..(horizon - 1), &eq_at(best, any, spell, &1))
  end

  defp eq_false(best, spell) do
    """
    (match (#{best} #{spell} 0) motive (λ _ → Bool)
      | true => false
      | false => true)
    """
  end

  defp eq_at(best, any, spell, j) do
    """
    (match (#{best} #{spell} #{j + 1}) motive (λ _ → Bool)
      | true => #{any} #{spell} #{j}
      | false =>
          (match (#{any} #{spell} #{j}) motive (λ _ → Bool)
            | true => false
            | false => true))
    """
  end

  defp band([one]), do: one

  defp band(cells) do
    mid = div(length(cells), 2)
    {left, right} = Enum.split(cells, mid)

    """
    (match (#{band(left)}) motive (λ _ → Bool)
      | true => #{band(right)}
      | false => false)
    """
  end

  defp agree_block(agrees, holds, body) do
    """
    def #{agrees} : run Bool :=
      #{body}
    def #{holds} : evidence {#{agrees} ≡ true : Bool} := refl
    """
  end

  defp prepare(host, states) do
    steps = step_table(host, states)

    if closed?(states, steps) do
      {:ok, bits(host, states, steps)}
    else
      :recur
    end
  end

  defp step_table(host, states) do
    Map.new(states, fn state ->
      row =
        Enum.map(host.actions, fn action ->
          {next, reward} = host.step.(state, action)
          {next, reward}
        end)

      {key(state), row}
    end)
  end

  defp closed?(states, steps) do
    known = MapSet.new(states, &key/1)

    Enum.all?(steps, fn {_key, row} ->
      Enum.all?(row, fn {next, _reward} -> MapSet.member?(known, key(next)) end)
    end)
  end

  # `rows[k]` is `best_pos(s, k + 1)`: some action pays now, or the
  # successor's bit at the previous horizon is set. Horizon 0 is the
  # false base and is not stored.
  defp bits(host, states, steps) do
    keys = Enum.map(states, &key/1)

    if host.horizon == 0 do
      Map.new(keys, &{&1, []})
    else
      prev = Map.new(keys, &{&1, false})

      {rows, _prev} =
        Enum.reduce(1..host.horizon, {Map.new(keys, &{&1, []}), prev}, fn _k, {rows, prev} ->
          layer =
            Map.new(keys, fn kstate ->
              bit =
                Enum.any?(Map.fetch!(steps, kstate), fn {next, reward} ->
                  positive?(reward) or Map.fetch!(prev, key(next))
                end)

              {kstate, bit}
            end)

          rows =
            Map.new(keys, fn kstate ->
              {kstate, Map.fetch!(rows, kstate) ++ [Map.fetch!(layer, kstate)]}
            end)

          {rows, layer}
        end)

      rows
    end
  end

  defp bits_of(bits, state), do: Map.fetch!(bits, key(state))

  defp positive?(0), do: false
  defp positive?({:suc, _n}), do: true
  defp positive?(n) when is_integer(n), do: n > 0
  defp positive?(_reward), do: false

  defp cover(host) do
    case Muro.Synth.Oracle.cover(host) do
      states when is_list(states) -> Enum.uniq_by(states, &key/1)
      _ -> []
    end
  end

  defp tabulate?(host, states, actions) do
    is_integer(host[:horizon]) and host.horizon >= 0 and host[:schema] != nil and
      states != [] and length(states) <= @domain_cap and actions != []
  end

  defp actions_of(host) do
    if is_list(host[:actions]), do: host.actions, else: []
  end

  defp key(%Term{value: value}), do: value
  defp key(other), do: other

  defp word(true), do: "true"
  defp word(false), do: "false"

  defp paren(spell) do
    cond do
      String.starts_with?(spell, "(") -> spell
      String.contains?(spell, " ") or String.contains?(spell, "\n") -> "(#{spell})"
      true -> spell
    end
  end
end
