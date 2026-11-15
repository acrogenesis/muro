defmodule Muro.Synth.Placement do
  @moduledoc false

  # A horizon-bounded combinatorial placement, recognized from `step`
  # and the shape of `State`. Nothing here names an environment.
  #
  # One constructor is an open list of Nat. One nullary constructor is
  # an absorbing zero. One constructor is an absorbing positive reward
  # on a list of that same Nat, every such list the same length, and
  # that length is the horizon. An action appends one Nat. The Nat is
  # read off a transition that stays a list. The constraint is the
  # disjunction of the `pair-any` templates that are false on every
  # open or finished list. The goal is the template that holds on every
  # finished list and fails on every shorter open list. Both are read
  # by `eval`. `placed-find-policy` is the run. The emitted policy is
  # run on every cover state and kept only when it takes the action the
  # trace order picks. The homomorphism is evidence about that run.
  #
  # A book that is not this shape is `:skip`, and the ranking loop
  # continues. A book that is this shape is not handed to that loop:
  # a later test of a raw Nat would memorize the cover.

  alias Muro.Synth.{Book, Cert, Feature, Oracle, Term}

  @max_states 32
  @max_cells 512
  @list {:list, :nat}

  @pred_names ~w(andb orb notb PredProg feat andp orp notp truep falsep eval)

  def attempt(host, oracle, anchor, checker, fuel, structural) do
    cond do
      oracle != "trace" or structural == false -> :skip
      true -> classify(host, anchor, checker, fuel)
    end
  end

  @doc false
  def play(model, config, steps) when is_map(model) and is_list(config) and is_integer(steps) do
    {actions, _memo} = rollout(model, {:open, config}, steps, %{})
    actions
  end

  @doc false
  def dead?(model, config), do: fires?(model.dead, config)

  @doc false
  def solved?(model, config), do: fires?(model.goal, config) and not dead?(model, config)

  defp classify(host, anchor, checker, fuel) do
    case recognize(host) do
      :skip ->
        :skip

      {:ok, shape} ->
        case discover(host, shape) do
          :skip ->
            :skip

          {:ok, found} ->
            case Oracle.observe(host, "trace", []) do
              {:ok, spec} ->
                judge(host, shape, found, spec, anchor, checker, fuel)

              _ ->
                :skip
            end
        end
    end
  end

  defp judge(host, shape, found, spec, anchor, checker, fuel) do
    winners = winner_map(host, spec)
    model = model(host, shape, found)

    # The size gate is first. Agreement walks the cover, and so does
    # running the emitted policy. A cover that cannot be split does
    # not pay for either.
    cond do
      too_big?(spec.cover, host.actions) ->
        refuse(
          found,
          nil,
          "the cover is too large for a case-split homomorphism"
        )

      not agree?(model, winners, spec.cover, shape) ->
        refuse(found, nil, "the discovered policy and the trace order disagree")

      true ->
        certify(host, shape, found, model, winners, anchor, checker, fuel)
    end
  end

  defp too_big?(states, actions) do
    n = length(states)
    a = length(actions)
    n > @max_states or n * a * a > @max_cells
  end

  defp certify(host, shape, found, model, winners, anchor, checker, fuel) do
    case render(host, shape, found, winners, anchor) do
      {:error, reason} ->
        refuse(found, nil, reason)

      {:ok, source, meta} ->
        case Book.check(source, anchor, fn path -> checker.(path, fuel) end) do
          :ok ->
            case deployed_agrees?(source, anchor, host, winners, meta.policy, fuel) do
              :ok ->
                found = Map.put(found, :winners, winners)
                done(:certified, found, source, meta.certificate, nil, model)

              {:error, :storage, diagnostic} ->
                {:error, :storage, diagnostic}

              {:error, reason} ->
                # The book may contain a CoindHomo for the trace order.
                # That is not a certificate for a policy that took
                # another action, so the book is not returned.
                refuse(found, nil, reason)
            end

          {:error, :storage, diagnostic} ->
            {:error, :storage, diagnostic}

          {:error, text} ->
            refuse(found, source, text)
        end
    end
  end

  defp refuse(found, book, reason) do
    done(:refused, found, book, nil, reason, Map.get(found, :model))
  end

  defp done(status, found, book, certificate, reason, model) do
    counts = found.counts
    play = if model, do: play(model, [], model.horizon), else: []

    lines =
      header(status, reason) ++
        [
          "program: #{Muro.Synth.render(found.program)}",
          "goal: #{Muro.Synth.render(found.goal)}",
          "enumerated #{counts.enumerated}",
          "alive #{counts.alive}",
          "reduced #{counts.reduced}",
          "solved #{counts.solved}",
          "cover #{counts.cover}"
        ] ++
        preferences(found) ++
        play_line(play) ++
        certificate_line(certificate)

    {:done,
     %{
       status: status,
       program: found.program,
       book: book,
       lines: lines,
       versions: [counts.enumerated, counts.alive, counts.reduced, counts.solved],
       cex: [],
       certificate: certificate,
       reason: reason,
       model: model,
       counts: counts
     }}
  end

  defp header(:certified, _reason), do: ["muro synth: homomorphism checked"]

  defp header(:refused, reason) do
    ["muro synth: placement policy was not certified", reason]
  end

  defp certificate_line(nil), do: []
  defp certificate_line(name), do: ["certificate #{name}"]

  defp play_line([]), do: []

  defp play_line(actions) do
    ["from the empty board the policy plays #{Enum.join(actions, " ")}"]
  end

  defp preferences(%{winners: winners}) when is_map(winners) do
    winners
    |> Enum.sort_by(fn {state, _action} -> Term.spell(state) end)
    |> Enum.map(fn {state, action} ->
      "at #{Term.spell(state)} the program prefers #{action}"
    end)
  end

  defp preferences(_found), do: []

  defp winner_map(host, spec) do
    Map.new(spec.cover, fn state ->
      action =
        Enum.find_value(spec.tasks, host.default, fn task ->
          case List.keyfind(task.observations, state, 0) do
            {^state, true} -> task.action
            _ -> nil
          end
        end)

      {state, action}
    end)
  end

  defp agree?(model, winners, states, shape) do
    {ok, _memo} =
      Enum.reduce_while(states, {true, %{}}, fn state, {_flag, memo} ->
        phase = phase_of(shape, state)
        {got, memo} = find_policy(model, phase, model.horizon, memo)

        if got == Map.fetch!(winners, state),
          do: {:cont, {true, memo}},
          else: {:halt, {false, memo}}
      end)

    ok
  end

  # The trace order and the Elixir finder can agree while the run that
  # was written does not. Exit 0 requires this comparison. The policy
  # is the run a caller invokes on a state.
  defp deployed_agrees?(source, anchor, host, winners, policy, fuel) do
    case File.mkdir_p(anchor) do
      :ok ->
        path =
          Path.join(anchor, "placed-agree-#{System.unique_integer([:positive])}.muro")

        case File.write(path, source) do
          :ok ->
            try do
              run_deployed(path, host, winners, policy, fuel)
            after
              _ = File.rm(path)
            end

          {:error, reason} ->
            {:error, :storage,
             "could not write a temporary book in #{anchor}: #{inspect(reason)}"}
        end

      {:error, reason} ->
        {:error, :storage, "could not write a temporary book in #{anchor}: #{inspect(reason)}"}
    end
  end

  defp run_deployed(path, host, winners, policy, fuel) do
    module = Module.concat(__MODULE__, "D#{System.unique_integer([:positive])}")

    case Muro.emit_file(path, module, fuel: fuel) do
      {:ok, src} ->
        try do
          Code.eval_string(src)
          compare_policy(module, host, winners, policy)
        rescue
          error ->
            {:error, "the deployed policy did not run (#{Exception.message(error)})"}
        end

      {:error, message} ->
        {:error, "the deployed policy did not emit (#{message})"}
    end
  end

  defp compare_policy(module, host, winners, policy) do
    fun = String.to_atom(Muro.Emit.elixir_base(policy))

    Enum.reduce_while(winners, :ok, fn {state, action}, :ok ->
      got = apply(module, fun, [emit_state(host, state)])
      want = String.to_atom(Muro.Emit.elixir_atom_name(action))

      if got == want do
        {:cont, :ok}
      else
        {:halt,
         {:error,
          "the deployed policy and the certified choices disagree at #{Term.spell(state)}"}}
      end
    end)
  end

  defp emit_state(host, %Term{value: value}) do
    if host.structured do
      Term.to_emit(host.schema, value)
    else
      String.to_atom(Muro.Emit.elixir_atom_name(to_string(value)))
    end
  end

  defp emit_state(_host, state) when is_binary(state) do
    String.to_atom(Muro.Emit.elixir_atom_name(state))
  end

  defp model(host, shape, found) do
    %{
      actions: host.actions,
      default: host.default,
      horizon: shape.length,
      columns: shape.columns,
      reward: shape.reward,
      dead: found.dead,
      goal: found.goal_specs,
      leb: host.leb
    }
  end

  # --- recognition -------------------------------------------------------

  defp recognize(host) do
    with {:data, _, rows} <- host.schema,
         false <- Enum.any?(rows, & &1[:erased]),
         {:ok, shape} <- shape(rows),
         states <- Oracle.cover(host),
         true <- states != [] and host.actions != [],
         {:ok, groups} <- groups(states, shape),
         {:ok, shape} <- sinks(host, shape, groups),
         {:ok, shape} <- columns(host, shape, shape.open_states),
         true <- host.horizon == shape.length do
      {:ok, shape}
    else
      _ -> :skip
    end
  end

  # The two list constructors are told apart by their rewards, not by
  # the order they were declared in. This only collects the names.
  defp shape(rows) do
    nullary = Enum.filter(rows, &(fields(&1) == []))
    listed = Enum.filter(rows, &list_field?/1)

    if length(rows) == 3 and length(nullary) == 1 and length(listed) == 2 do
      {:ok, %{zero: hd(nullary).name, listed: Enum.map(listed, & &1.name)}}
    else
      :skip
    end
  end

  defp fields(%{fields: fields}), do: fields
  defp list_field?(%{fields: [field]}), do: field_schema(field) == @list
  defp list_field?(_row), do: false

  defp field_schema(%{schema: schema}), do: schema
  defp field_schema(schema), do: schema

  defp groups(states, shape) do
    Enum.reduce_while(states, {:ok, %{zero: [], listed: %{}}}, fn state, {:ok, acc} ->
      case unpack(state) do
        {:atom, atom} ->
          if atom == atom_of(shape.zero) do
            {:cont, {:ok, %{acc | zero: acc.zero ++ [state]}}}
          else
            {:halt, :skip}
          end

        {:list, atom, config} ->
          if atom in Enum.map(shape.listed, &atom_of/1) do
            bucket = Map.get(acc.listed, atom, [])

            {:cont,
             {:ok, %{acc | listed: Map.put(acc.listed, atom, bucket ++ [{state, config}])}}}
          else
            {:halt, :skip}
          end

        :error ->
          {:halt, :skip}
      end
    end)
  end

  defp sinks(host, shape, groups) do
    with true <- groups.zero != [],
         true <- zero_sink?(host, groups.zero),
         {:ok, open_name, solved_name, reward, length} <-
           split_lists(host, shape.listed, groups.listed) do
      {:ok,
       %{
         zero: shape.zero,
         open: open_name,
         solved: solved_name,
         reward: reward,
         length: length,
         zero_states: groups.zero,
         open_states: Map.get(groups.listed, atom_of(open_name), []),
         solved_states: Map.get(groups.listed, atom_of(solved_name), [])
       }}
    else
      _ -> :skip
    end
  end

  defp zero_sink?(host, states) do
    Enum.all?(states, fn state ->
      Enum.all?(host.actions, fn action ->
        {next, reward} = host.step.(state, action)
        same?(next, state) and nat_of(reward) == {:ok, 0}
      end)
    end)
  end

  defp split_lists(host, names, listed) do
    named =
      Enum.map(names, fn name ->
        rows = Map.get(listed, atom_of(name), [])
        {name, rows, absorb(host, rows)}
      end)

    case named do
      [{left, left_rows, {:open, _}}, {right, _right_rows, {:solved, reward, full}}] ->
        if open_shape?(left_rows, full),
          do: {:ok, left, right, reward, full},
          else: :skip

      [{left, _left_rows, {:solved, reward, full}}, {right, right_rows, {:open, _}}] ->
        if open_shape?(right_rows, full),
          do: {:ok, right, left, reward, full},
          else: :skip

      _ ->
        :skip
    end
  end

  defp absorb(_host, []), do: :skip

  defp absorb(host, rows) do
    sample = hd(rows)

    case sink_reward(host, elem(sample, 0)) do
      {:ok, 0} ->
        :not_positive

      {:ok, reward} ->
        lens = Enum.map(rows, fn {_state, config} -> length(config) end)

        if Enum.uniq(lens) == [hd(lens)] and
             Enum.all?(rows, fn {state, _config} -> sink_reward(host, state) == {:ok, reward} end) do
          {:solved, reward, hd(lens)}
        else
          :skip
        end

      # The move that finishes pays the positive reward and leaves, so an
      # open state is not a sink. It is not required to pay zero on every
      # action.
      :open ->
        if Enum.all?(rows, fn {state, _config} -> sink_reward(host, state) == :open end) do
          {:open, Enum.map(rows, fn {_state, config} -> length(config) end)}
        else
          :skip
        end
    end
  end

  defp sink_reward(host, state) do
    rows =
      Enum.map(host.actions, fn action ->
        {next, reward} = host.step.(state, action)
        {same?(next, state), nat_of(reward)}
      end)

    cond do
      rows != [] and positive_sink?(rows) -> elem(hd(rows), 1)
      rows != [] and Enum.all?(rows, &match?({true, {:ok, 0}}, &1)) -> {:ok, 0}
      true -> :open
    end
  end

  defp positive_sink?(rows) do
    Enum.all?(rows, fn
      {true, {:ok, n}} when n > 0 -> true
      _ -> false
    end) and one_reward?(rows)
  end

  defp one_reward?(rows) do
    rows
    |> Enum.map(fn
      {_same, {:ok, n}} -> n
      _ -> :bad
    end)
    |> Enum.uniq()
    |> length() == 1
  end

  defp open_shape?(rows, full) do
    rows != [] and Enum.all?(rows, fn {_state, config} -> length(config) < full end)
  end

  defp columns(host, shape, open_states) do
    Enum.reduce_while(host.actions, {:ok, %{}}, fn action, {:ok, acc} ->
      case column_of(host, shape, open_states, action) do
        {:ok, col} -> {:cont, {:ok, Map.put(acc, action, col)}}
        :skip -> {:halt, :skip}
      end
    end)
    |> case do
      {:ok, cols} -> {:ok, Map.put(shape, :columns, cols)}
      :skip -> :skip
    end
  end

  defp column_of(host, shape, open_states, action) do
    kept = MapSet.new([atom_of(shape.open), atom_of(shape.solved)])

    cols =
      Enum.flat_map(open_states, fn {state, config} ->
        {next, _reward} = host.step.(state, action)

        case unpack(next) do
          {:list, atom, ys} ->
            if MapSet.member?(kept, atom) do
              case snoc_col(config, ys) do
                {:ok, col} -> [col]
                :error -> [:bad]
              end
            else
              []
            end

          _ ->
            []
        end
      end)

    case Enum.uniq(cols) do
      [col] when is_integer(col) -> {:ok, col}
      _ -> :skip
    end
  end

  defp snoc_col(xs, ys) do
    if length(ys) == length(xs) + 1 and Enum.drop(ys, -1) == xs do
      {:ok, List.last(ys)}
    else
      :error
    end
  end

  # --- discovery ---------------------------------------------------------

  defp discover(host, shape) do
    alive = Enum.map(shape.open_states ++ shape.solved_states, &elem(&1, 1))
    solved = Enum.map(shape.solved_states, &elem(&1, 1))
    open = Enum.map(shape.open_states, &elem(&1, 1))
    values = Enum.map(alive, &encode/1)
    taken = taken_names(host.book)
    {specs, _taken} = Term.templates(@list, values, taken, 0)

    kept = Enum.filter(specs, &(not Enum.any?(alive, fn config -> bit?(&1, config) end)))
    reduced = Feature.eliminate_redundant(kept)

    goals =
      Enum.filter(specs, fn spec ->
        Enum.all?(solved, &bit?(spec, &1)) and Enum.all?(open, &(not bit?(spec, &1)))
      end)

    found = %{
      dead: reduced,
      goal_specs: goals,
      program: nest(reduced),
      goal: nest(goals),
      counts: %{
        enumerated: length(specs),
        alive: length(kept),
        reduced: length(reduced),
        solved: length(goals),
        cover: length(Oracle.cover(host))
      }
    }

    if verify?(host, shape, found),
      do: {:ok, Map.put(found, :model, model(host, shape, found))},
      else: :skip
  end

  defp verify?(host, shape, found) do
    open_ok =
      Enum.all?(shape.open_states, fn {state, config} ->
        Enum.all?(host.actions, fn action ->
          {next, reward} = host.step.(state, action)
          replay(host, shape, found, config, action, next, reward)
        end)
      end)

    sinks_ok =
      zero_sink?(host, shape.zero_states) and
        Enum.all?(shape.solved_states, fn {state, _config} ->
          sink_reward(host, state) == {:ok, shape.reward}
        end)

    open_ok and sinks_ok and found.goal_specs != []
  end

  defp replay(_host, shape, found, config, action, next, reward) do
    col = Map.fetch!(shape.columns, action)
    ys = config ++ [col]

    cond do
      fires?(found.dead, ys) ->
        zero_next?(shape, next) and nat_of(reward) == {:ok, 0}

      fires?(found.goal_specs, ys) ->
        case unpack(next) do
          {:list, atom, ^ys} ->
            atom == atom_of(shape.solved) and nat_of(reward) == {:ok, shape.reward}

          _ ->
            false
        end

      true ->
        case unpack(next) do
          {:list, atom, ^ys} -> atom == atom_of(shape.open) and nat_of(reward) == {:ok, 0}
          _ -> false
        end
    end
  end

  defp zero_next?(shape, next) do
    case unpack(next) do
      {:atom, atom} -> atom == atom_of(shape.zero)
      _ -> false
    end
  end

  defp bit?(spec, config), do: Term.eval_spec(@list, spec, encode(config))
  defp fires?(specs, config), do: Enum.any?(specs, &bit?(&1, config))

  defp nest([]), do: false
  defp nest([spec]), do: {:feat, spec.name}

  defp nest([spec | rest]) do
    {:or, {:feat, spec.name}, nest(rest)}
  end

  # --- policy book -------------------------------------------------------

  defp render(host, shape, found, winners, anchor) do
    taken = taken_names(host.book)

    if Enum.any?(@pred_names, &MapSet.member?(taken, &1)) or host.defined_carrier or
         host.defined_feature or host.defined_eval do
      {:error, "the environment already defines the predicate language"}
    else
      used = found.dead ++ found.goal_specs
      {helpers, taken} = Term.render_helpers(used, taken)
      taken = claim_monus(taken, helpers)
      {rows, taken, spell} = feature_rows(used, taken)
      names = standard_names()
      {names, taken} = reserve_names(names, taken)
      source = book_source(host, shape, found, names, helpers, rows, spell, anchor)
      host = Map.put(host, :winners, winners)
      arm = dummy_arm(host, found.program)

      case Cert.render(host, [arm], "trace", %{
             taken: taken,
             names: names,
             decl: %{},
             policy: names.policy
           }) do
        {:ok, cert} ->
          {:ok, source <> "\n" <> cert.text,
           %{certificate: cert.certificate, policy: names.policy}}

        {:skip, reason} ->
          {:error, reason}
      end
    end
  end

  defp claim_monus(taken, %{funs: %{nat_abs: name}}) when is_binary(name) do
    claim(taken, name <> "-monus")
  end

  defp claim_monus(taken, _helpers), do: taken

  defp feature_rows(specs, taken) do
    Enum.reduce(specs, {[], taken, %{}}, fn spec, {rows, taken, spell} ->
      {ctor, taken} = Book.reserve(spec.name, taken)
      {rows ++ [%{spec: spec, ctor: ctor}], taken, Map.put(spell, spec.name, ctor)}
    end)
  end

  defp dummy_arm(host, program) do
    %{
      name: "survivor",
      pred: program,
      action: hd(host.actions),
      else: host.default,
      observations: Enum.map(Oracle.cover(host), &{&1, false}),
      kept: [program]
    }
  end

  defp standard_names do
    %{
      pred: "PredProg",
      feat: "feat",
      andp: "andp",
      orp: "orp",
      notp: "notp",
      truep: "truep",
      falsep: "falsep",
      eval: "eval",
      andb: "andb",
      orb: "orb",
      notb: "notb"
    }
  end

  defp reserve_names(names, taken) do
    bases = [
      :survivor,
      :goal,
      :policy,
      :phase,
      :moving,
      :lost,
      :won,
      :snoc,
      :column,
      :extend,
      :after,
      :judge,
      :step,
      :trace,
      :lex,
      :trace_le,
      :trace_max,
      :max_helper,
      :max_trace,
      :best,
      :trace_action,
      :insert,
      :insert_cons,
      :sort,
      :scored,
      :ranking,
      :find
    ]

    words = %{
      survivor: "survivor",
      goal: "goal",
      policy: "policy",
      phase: "Phase",
      moving: "moving",
      lost: "lost",
      won: "won",
      snoc: "placed-snoc",
      column: "placed-column",
      extend: "placed-extend",
      after: "placed-after",
      judge: "placed-judge",
      step: "placed-step",
      trace: "placed-trace",
      lex: "placed-lex-step",
      trace_le: "placed-trace-le",
      trace_max: "placed-trace-max",
      max_helper: "placed-max-helper",
      max_trace: "placed-max-trace",
      best: "placed-best-trace",
      trace_action: "placed-trace-action",
      insert: "placed-insert",
      insert_cons: "placed-insert-cons",
      sort: "placed-sort-scored",
      scored: "placed-scored",
      ranking: "placed-find-ranking",
      find: "placed-find-policy"
    }

    Enum.reduce(bases, {names, taken}, fn key, {names, taken} ->
      {reserved, taken} = Book.reserve(Map.fetch!(words, key), taken)
      {Map.put(names, key, reserved), taken}
    end)
  end

  defp book_source(host, shape, found, names, helpers, rows, spell, anchor) do
    """
    -- The survivor is the constraint the search discovered.
    -- goal is the length that finishes a placement.
    -- placed-find-policy is the run. policy runs it on a state.
    -- Both are checked against the action the trace order picks.
    -- The homomorphism is evidence about that run, and only when
    -- those actions agree.
    -- The checker sees this book. It does not see the search.
    import "#{rel(anchor, host.path)}"

    def Carrier : spec Type := List Nat
    #{helpers.text}
    data Feature : Type where
    #{Enum.map_join(rows, "\n", &"  #{&1.ctor} : Feature")}

    def eval-feature : run Π (+ f : Feature) → Π (+ c : Carrier) → Bool :=
      λ (+ f : Feature) → λ (+ c : Carrier) →
        match f motive (λ _ → Bool)
    #{Enum.map_join(rows, "\n", &Term.render_clause(@list, &1.spec, &1.ctor, helpers))}
    #{Book.evaluator()}
    def #{names.survivor} : run #{names.pred} := #{spell_pred(names, spell, found.program)}
    def #{names.goal} : run #{names.pred} := #{spell_pred(names, spell, found.goal)}
    #{dynamics(names, shape, host)}
    #{finder(names)}
    def #{names.policy} : run Π (+ s : State) → Action :=
      λ (+ s : State) →
        match s motive (λ _ → Action)
    #{policy_arms(names, host, shape)}
    """
  end

  defp dynamics(names, shape, host) do
    reward = Integer.to_string(shape.reward)

    arms =
      host
      |> action_ctors()
      |> Enum.map_join("\n", fn ctor ->
        "      | #{ctor} => #{Map.fetch!(shape.columns, ctor)}"
      end)

    """
    data #{names.phase} : Type where
      #{names.moving} : Π (xs : List Nat) → #{names.phase}
      #{names.lost} : #{names.phase}
      #{names.won} : Π (xs : List Nat) → #{names.phase}

    def #{names.snoc} : run Π (+ xs : List Nat) → Π (+ x : Nat) → List Nat :=
      λ (+ xs : List Nat) → λ (+ x : Nat) →
        match xs motive (λ _ → List Nat)
          | nil => cons x nil
          | cons y ys => cons y (#{names.snoc} ys x)

    def #{names.column} : run Π (+ a : Action) → Nat :=
      λ (+ a : Action) →
        match a motive (λ _ → Nat)
    #{arms}

    def #{names.extend} : run Π (+ xs : List Nat) → Π (+ a : Action) → List Nat :=
      λ (+ xs : List Nat) → λ (+ a : Action) → #{names.snoc} xs (#{names.column} a)

    def #{names.after} : run Π (+ ys : List Nat) → #{names.phase} × Reward :=
      λ (+ ys : List Nat) →
        (match (#{names.eval} #{names.survivor} ys) motive (λ _ → #{names.phase} × Reward)
          | true => (#{names.lost}, 0)
          | false =>
              (match (#{names.eval} #{names.goal} ys) motive (λ _ → #{names.phase} × Reward)
                | true => (#{names.won} ys, #{reward})
                | false => (#{names.moving} ys, 0)))

    def #{names.judge} : run Π (+ xs : List Nat) → Π (+ a : Action) → #{names.phase} × Reward :=
      λ (+ xs : List Nat) → λ (+ a : Action) → #{names.after} (#{names.extend} xs a)

    def #{names.step} : run Π (p : #{names.phase}) → Π (a : Action) → #{names.phase} × Reward :=
      λ (p : #{names.phase}) → λ (a : Action) →
        match p motive (λ _ → #{names.phase} × Reward)
          | #{names.moving} xs => #{names.judge} xs a
          | #{names.lost} => (#{names.lost}, 0)
          | #{names.won} xs => (#{names.won} xs, #{reward})
    """
  end

  defp finder(n) do
    """
    def #{n.trace} : spec Type := List Reward

    def #{n.lex} : run Π (+ r1 : Reward) → Π (+ r2 : Reward) → Π (rest : Unit → Bool) → Bool :=
      λ (+ r1 : Reward) → λ (+ r2 : Reward) → λ (rest : Unit → Bool) →
        match leb r1 r2 motive (λ _ → Bool)
          | true => (match leb r2 r1 motive (λ _ → Bool) | true => rest tt | false => true)
          | false => false

    def #{n.trace_le} : run Π (t1 : #{n.trace}) → Π (t2 : #{n.trace}) → Bool :=
      λ (t1 : #{n.trace}) → λ (t2 : #{n.trace}) →
        match t1 motive (λ _ → Bool)
          | nil => true
          | cons r1 u1 =>
              (match t2 motive (λ _ → Bool)
                | nil => false
                | cons r2 u2 => #{n.lex} r1 r2 (λ (_ : Unit) → #{n.trace_le} u1 u2))

    def #{n.trace_max} : run Π (+ current : #{n.trace}) → Π (+ t : #{n.trace}) → #{n.trace} :=
      λ (+ current : #{n.trace}) → λ (+ t : #{n.trace}) →
        match #{n.trace_le} current t motive (λ _ → #{n.trace}) | true => t | false => current

    def #{n.max_helper} : run Π (+ current : #{n.trace}) → Π (ts : List #{n.trace}) → #{n.trace} :=
      λ (+ current : #{n.trace}) → λ (ts : List #{n.trace}) →
        match ts motive (λ _ → #{n.trace})
          | nil => current
          | cons t rest => #{n.max_helper} (#{n.trace_max} current t) rest

    def #{n.max_trace} : run Π (ts : List #{n.trace}) → #{n.trace} :=
      λ (ts : List #{n.trace}) →
        match ts motive (λ _ → #{n.trace}) | nil => nil | cons t rest => #{n.max_helper} t rest

    def #{n.best} : run Π (+ s : #{n.phase}) → Π (+ k : Nat) → #{n.trace} :=
      λ (+ s : #{n.phase}) → λ (+ k : Nat) →
        match k motive (λ _ → #{n.trace})
          | 0 => nil
          | suc j => #{n.max_trace} (map Action #{n.trace} (λ (a : Action) → #{n.trace_action} s a j) all-actions)

    def #{n.trace_action} : run Π (+ s : #{n.phase}) → Π (+ a : Action) → Π (+ k : Nat) → #{n.trace} :=
      λ (+ s : #{n.phase}) → λ (+ a : Action) → λ (+ k : Nat) →
        cons (snd (#{n.step} s a)) (#{n.best} (fst (#{n.step} s a)) k)

    def #{n.insert} : run Π (+ x : Action × #{n.trace}) → Π (xs : List (Action × #{n.trace})) → List (Action × #{n.trace}) :=
      λ (+ x : Action × #{n.trace}) → λ (xs : List (Action × #{n.trace})) →
        match xs motive (λ _ → List (Action × #{n.trace}))
          | nil => cons x nil
          | cons y ys => #{n.insert_cons} x y ys

    def #{n.insert_cons} : run Π (+ x : Action × #{n.trace}) → Π (+ y : Action × #{n.trace}) → Π (+ ys : List (Action × #{n.trace})) → List (Action × #{n.trace}) :=
      λ (+ x : Action × #{n.trace}) → λ (+ y : Action × #{n.trace}) → λ (+ ys : List (Action × #{n.trace})) →
        match #{n.trace_le} (snd y) (snd x) motive (λ _ → List (Action × #{n.trace}))
          | true => cons x (cons y ys)
          | false => cons y (#{n.insert} x ys)

    def #{n.sort} : run Π (xs : List (Action × #{n.trace})) → List (Action × #{n.trace}) :=
      λ (xs : List (Action × #{n.trace})) →
        match xs motive (λ _ → List (Action × #{n.trace}))
          | nil => nil
          | cons x rest => #{n.insert} x (#{n.sort} rest)

    def #{n.scored} : run Π (+ s : #{n.phase}) → Π (+ k : Nat) → Π (+ a : Action) → Action × #{n.trace} :=
      λ (+ s : #{n.phase}) → λ (+ k : Nat) → λ (+ a : Action) → (a, #{n.trace_action} s a k)

    def #{n.ranking} : run Π (+ s : #{n.phase}) → Π (+ k : Nat) → List Action :=
      λ (+ s : #{n.phase}) → λ (+ k : Nat) →
        map (Action × #{n.trace}) Action (λ (p : Action × #{n.trace}) → fst p)
          (#{n.sort} (map Action (Action × #{n.trace}) (λ (a : Action) → #{n.scored} s k a) all-actions))

    def #{n.find} : run Π (+ s : #{n.phase}) → Π (+ k : Nat) → Action :=
      λ (+ s : #{n.phase}) → λ (+ k : Nat) →
        match #{n.ranking} s k motive (λ _ → Action) | nil => default-action | cons a rest => a
    """
  end

  defp policy_arms(names, host, shape) do
    host
    |> state_ctors()
    |> Enum.map_join("\n", fn ctor ->
      cond do
        ctor == shape.open ->
          "      | #{ctor} xs => #{names.find} (#{names.moving} xs) horizon"

        ctor == shape.zero ->
          "      | #{ctor} => #{names.find} #{names.lost} horizon"

        ctor == shape.solved ->
          "      | #{ctor} xs => #{names.find} (#{names.won} xs) horizon"
      end
    end)
  end

  defp state_ctors(host) do
    case host.schema do
      {:data, _, rows} -> Enum.map(rows, & &1.name)
      _ -> []
    end
  end

  defp action_ctors(host) do
    case Enum.find(host.book, &(Map.get(&1, :kind) == :data and &1.name == "Action")) do
      %{ctors: ctors} -> Enum.map(ctors, & &1.name)
      _ -> host.actions
    end
  end

  defp spell_pred(names, _spell, false), do: names.falsep
  defp spell_pred(names, _spell, true), do: names.truep

  defp spell_pred(names, spell, {:feat, feature}) do
    "(#{names.feat} #{Map.fetch!(spell, feature)})"
  end

  defp spell_pred(names, spell, {:or, left, right}) do
    "(#{names.orp} #{spell_pred(names, spell, left)} #{spell_pred(names, spell, right)})"
  end

  # --- values ------------------------------------------------------------

  defp unpack(state) do
    case Term.value_of(state) do
      atom when is_atom(atom) ->
        {:atom, atom}

      value when is_tuple(value) and tuple_size(value) == 2 ->
        case list_nats(elem(value, 1)) do
          {:ok, config} -> {:list, elem(value, 0), config}
          :error -> :error
        end

      _ ->
        :error
    end
  end

  defp list_nats(nil), do: {:ok, []}

  defp list_nats({:cons, head, tail}) do
    with {:ok, n} <- nat_of(head), {:ok, rest} <- list_nats(tail), do: {:ok, [n | rest]}
  end

  defp list_nats(_), do: :error

  defp encode([]), do: nil
  defp encode([head | tail]), do: {:cons, head, encode(tail)}

  defp nat_of(0), do: {:ok, 0}
  defp nat_of(n) when is_integer(n) and n >= 0, do: {:ok, n}

  defp nat_of({:suc, n}) do
    case nat_of(n) do
      {:ok, k} -> {:ok, k + 1}
      :error -> :error
    end
  end

  defp nat_of(_), do: :error

  defp atom_of(name), do: String.to_atom(Muro.Emit.elixir_atom_name(name))

  defp same?(left, right), do: Term.value_of(left) == Term.value_of(right)

  defp phase_of(shape, state) do
    case unpack(state) do
      {:atom, _atom} ->
        :lost

      {:list, atom, config} ->
        cond do
          atom == atom_of(shape.solved) -> {:won, config}
          atom == atom_of(shape.open) -> {:open, config}
          true -> :lost
        end

      :error ->
        :lost
    end
  end

  # --- finder, executed --------------------------------------------------

  defp rollout(_model, _phase, 0, memo), do: {[], memo}

  defp rollout(model, phase, steps, memo) do
    {action, memo} = find_policy(model, phase, model.horizon, memo)
    {next, _reward, memo} = phase_step(model, phase, action, memo)
    {rest, memo} = rollout(model, next, steps - 1, memo)
    {[action | rest], memo}
  end

  defp find_policy(model, phase, k, memo) do
    {ranked, memo} = ranking(model, phase, k, memo)

    case ranked do
      [] -> {model.default, memo}
      [{action, _trace} | _] -> {action, memo}
    end
  end

  defp ranking(model, phase, k, memo) do
    {scored, memo} =
      Enum.map_reduce(model.actions, memo, fn action, memo ->
        {trace, memo} = trace_action(model, phase, action, k, memo)
        {{action, trace}, memo}
      end)

    {sort_scored(model, scored), memo}
  end

  defp sort_scored(_model, []), do: []

  defp sort_scored(model, [head | tail]) do
    insert(model, head, sort_scored(model, tail))
  end

  defp insert(_model, item, []), do: [item]

  defp insert(model, {_, xt} = item, [{_, yt} | _] = rest) do
    if trace_le(model, yt, xt) do
      [item | rest]
    else
      [hd(rest) | insert(model, item, tl(rest))]
    end
  end

  defp trace_action(model, phase, action, k, memo) do
    key = {:trace, phase, action, k}

    case Map.fetch(memo, key) do
      {:ok, trace} ->
        {trace, memo}

      :error ->
        {next, reward, memo} = phase_step(model, phase, action, memo)
        {rest, memo} = best_trace(model, next, k, memo)
        trace = [reward | rest]
        {trace, Map.put(memo, key, trace)}
    end
  end

  defp best_trace(_model, _phase, 0, memo), do: {[], memo}

  defp best_trace(_model, :lost, k, memo) do
    memo_best(memo, {:best, :lost, k}, fn -> List.duplicate(0, k) end)
  end

  defp best_trace(model, {:won, _}, k, memo) do
    memo_best(memo, {:best, :won, k}, fn -> List.duplicate(model.reward, k) end)
  end

  defp best_trace(model, phase, k, memo) do
    key = {:best, phase, k}

    case Map.fetch(memo, key) do
      {:ok, trace} ->
        {trace, memo}

      :error ->
        {traces, memo} =
          Enum.map_reduce(model.actions, memo, fn action, memo ->
            trace_action(model, phase, action, k - 1, memo)
          end)

        trace = Enum.reduce(traces, &trace_max(model, &1, &2))
        {trace, Map.put(memo, key, trace)}
    end
  end

  defp memo_best(memo, key, fun) do
    case Map.fetch(memo, key) do
      {:ok, trace} ->
        {trace, memo}

      :error ->
        trace = fun.()
        {trace, Map.put(memo, key, trace)}
    end
  end

  defp trace_max(model, left, right) do
    if trace_le(model, left, right), do: right, else: left
  end

  defp trace_le(_model, [], _right), do: true
  defp trace_le(_model, _left, []), do: false

  defp trace_le(model, [r1 | u1], [r2 | u2]) do
    cond do
      model.leb.(r1, r2) and model.leb.(r2, r1) -> trace_le(model, u1, u2)
      model.leb.(r1, r2) -> true
      true -> false
    end
  end

  defp phase_step(_model, :lost, _action, memo), do: {:lost, 0, memo}

  defp phase_step(model, {:won, config}, _action, memo), do: {{:won, config}, model.reward, memo}

  defp phase_step(model, {:open, config}, action, memo) do
    ys = config ++ [Map.fetch!(model.columns, action)]

    cond do
      fires?(model.dead, ys) -> {:lost, 0, memo}
      fires?(model.goal, ys) -> {{:won, ys}, model.reward, memo}
      true -> {{:open, ys}, 0, memo}
    end
  end

  # --- names -------------------------------------------------------------

  defp taken_names(book) do
    Enum.reduce(book, MapSet.new(), fn entry, acc ->
      Enum.reduce(entry_names(entry), acc, &claim(&2, &1))
    end)
  end

  defp entry_names(%{kind: :data, name: name, ctors: ctors}),
    do: [name | Enum.map(ctors, & &1.name)]

  defp entry_names(%{kind: :import}), do: []
  defp entry_names(%{name: name}), do: [name]
  defp entry_names(_entry), do: []

  defp claim(taken, name) do
    taken
    |> MapSet.put(name)
    |> MapSet.put({:elixir, Muro.Emit.elixir_base(name)})
  end

  defp rel(from_dir, to_file) do
    from = from_dir |> Path.expand() |> Path.split()
    to = to_file |> Path.expand() |> Path.split()
    {from, to} = drop_common(from, to)
    Path.join(List.duplicate("..", length(from)) ++ to)
  end

  defp drop_common([head | from], [head | to]), do: drop_common(from, to)
  defp drop_common(from, to), do: {from, to}
end
