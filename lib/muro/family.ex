defmodule Muro.Family do
  @moduledoc """
  Checks a keyed family.

  The declaration is spec. It names one buffered meeting and a closed
  kind, and one rule for each constructor. `always` is decided on the
  fixed script in `Muro.Family.Graph`. `eventually` and `leads_to` are
  `not yet decided`. A formula over a family that does not check is
  `skipped because <family> does not check`, and the formula is not walked.
  """

  @run_msg "temporal formulas do not mention run definitions"

  @doc """
  `:ok` when the meeting is buffered and checks, the kind is closed, and
  each constructor has one rule. `{:error, message}` otherwise. The
  message has no location and no declaration name.

  `status` is the meeting's recorded outcome: `:absent`, `:unchecked`,
  or `:ok`.
  """
  def check(book, %{meeting: meeting, key: key, rules: rules}, status) when is_list(book) do
    with :ok <- meeting_ok(meeting, status),
         :ok <- buffered(book, meeting),
         {:ok, data} <- closed_kind(book, key) do
      rules_ok(data, rules)
    end
  end

  @doc false
  def check_decl(book, %{meeting: meeting} = family, fuel) when is_list(book) do
    check(book, family, meeting_status(book, meeting, fuel))
  end

  @doc """
  The success line `family <name>: <meeting> per key of <kind>`.
  """
  def line(%{name: name, meeting: meeting, key: key}) do
    "family #{name}: #{meeting} per key of #{key}"
  end

  @doc """
  `{:ok, states, transitions}` when `always` holds on the family graph.
  `{:error, "not yet decided"}` when the formula is `eventually` or
  `leads_to`. `{:error, "skipped because <family> does not check"}` when
  `status` is the family's refusal: the formula is not walked.
  `{:error, message}` when a binder or an atom is not, or `always`
  fails. The message has no location and no declaration name.

  `status` is `check/3` or `check_decl/3`. The three-argument form
  checks the declaration, including its meeting. `prep` is a
  `Muro.Family.Graph` search shared by the declarations of one family,
  or `:auto` to build it here.
  """
  def judge_formula(book, family, formula) when is_list(book) do
    judge_formula(book, family, formula, check_decl(book, family, nil))
  end

  def judge_formula(book, family, formula, status) when is_list(book) do
    judge_formula(book, family, formula, status, :auto)
  end

  def judge_formula(book, %{key: key} = family, formula, :ok, prep) when is_list(book) do
    with {:ok, data} <- closed_kind(book, key),
         :ok <- walk_formula(book, data, %{}, formula) do
      decide(book, family, formula, prep)
    end
  end

  def judge_formula(_book, %{name: name}, _formula, {:error, _}, _prep) do
    {:error, "skipped because #{name} does not check"}
  end

  defp decide(book, family, formula, prep) do
    if always?(formula) do
      decide_always(book, family, formula, prep)
    else
      {:error, "not yet decided"}
    end
  end

  defp always?({:forall, _, _, body}), do: always?(body)
  defp always?({:always, _}), do: true
  defp always?(_), do: false

  defp decide_always(book, family, formula, :auto) do
    case Muro.Family.Graph.prepare(book, family) do
      {:ok, search} -> Muro.Family.Graph.decide(search, formula)
      {:error, _} = err -> err
    end
  end

  defp decide_always(_book, _family, formula, {:ok, search}) do
    Muro.Family.Graph.decide(search, formula)
  end

  defp decide_always(book, family, formula, :skip),
    do: decide_always(book, family, formula, :auto)

  defp decide_always(_book, _family, _formula, {:error, msg}), do: {:error, msg}

  defp meeting_ok(name, :absent), do: {:error, "unknown meeting #{name}"}
  defp meeting_ok(name, :unchecked), do: {:error, "skipped because #{name} does not check"}
  defp meeting_ok(_name, :ok), do: :ok

  defp meeting_status(book, name, fuel) do
    case Enum.find(book, &match?(%{kind: :meet, name: ^name}, &1)) do
      nil ->
        :absent

      meet ->
        case Muro.Check.check_def(book, meet, fuel) do
          :ok -> :ok
          {:note, _} -> :ok
          {:graph, _, _, _} -> :ok
          {:choreo, _} -> :ok
          {:error, _} -> :unchecked
        end
    end
  end

  defp buffered(book, name) do
    case Enum.find(book, &match?(%{kind: :meet, name: ^name}, &1)) do
      %{buffer: n} when is_integer(n) -> :ok
      %{kind: :meet} -> {:error, "family needs a buffered meeting"}
      _ -> {:error, "unknown meeting #{name}"}
    end
  end

  defp closed_kind(book, name) do
    case Enum.find(book, &(&1[:kind] == :data and &1.name == name)) do
      nil ->
        {:error, "unknown data type #{name}"}

      %{params: params, ctors: ctors} = data ->
        if ctors != [] and Enum.all?(ctors, &nullary?(&1, data)) and params_closed?(params) do
          {:ok, data}
        else
          {:error, "family over #{name} is not a closed kind"}
        end
    end
  end

  # The same stub `forall` uses. Parameters are allowed.
  defp params_closed?(_params), do: true

  defp nullary?(%{type: ty}, %{params: params}) do
    nullary_after?(ty, length(params))
  end

  defp nullary_after?({:pi, _, _, _, body}, n) when n > 0, do: nullary_after?(body, n - 1)
  defp nullary_after?({:pi, _, _, _, _}, 0), do: false
  defp nullary_after?(_, 0), do: true
  defp nullary_after?(_, _), do: false

  defp rules_ok(%{name: type_name, ctors: ctors}, rules) do
    names = MapSet.new(ctors, & &1.name)

    case rule_walk(rules, type_name, names, MapSet.new()) do
      {:error, _} = err ->
        err

      {:ok, seen} ->
        case Enum.find(ctors, fn ctor -> not MapSet.member?(seen, ctor.name) end) do
          nil -> :ok
          %{name: missing} -> {:error, "no rule for #{missing}"}
        end
    end
  end

  defp rule_walk([], _type_name, _names, seen), do: {:ok, seen}

  defp rule_walk([%{ctor: ctor} | rest], type_name, names, seen) do
    cond do
      not MapSet.member?(names, ctor) ->
        {:error, "#{ctor} is not a constructor of #{type_name}"}

      MapSet.member?(seen, ctor) ->
        {:error, "duplicate rule for #{ctor}"}

      true ->
        rule_walk(rest, type_name, names, MapSet.put(seen, ctor))
    end
  end

  # `key` is the sort, including when a data type of that name exists.
  defp bind(_book, {:dat, "key", []}), do: {:ok, :key}
  defp bind(_book, :bit), do: {:ok, :value}
  defp bind(_book, :nat), do: {:error, "forall over Nat ranges over an open type"}

  defp bind(book, {:dat, name, _}) do
    case Enum.find(book, &(&1[:kind] == :data and &1.name == name)) do
      %{params: params, ctors: ctors} = data ->
        if ctors != [] and Enum.all?(ctors, &nullary?(&1, data)) and params_closed?(params) do
          {:ok, :value}
        else
          {:error, "forall over #{name} ranges over an open type"}
        end

      _ ->
        {:error, "forall over #{name} ranges over an open type"}
    end
  end

  defp bind(_book, ty), do: {:error, "forall over #{ty_open(ty)} ranges over an open type"}

  defp ty_open(:unit), do: "Unit"
  defp ty_open({:vec, _, _}), do: "Vec"
  defp ty_open({:pair, _, _}), do: "a pair"
  defp ty_open({:rec, _}), do: "a record"
  defp ty_open(other), do: inspect(other)

  defp walk_formula(book, data, env, {:forall, x, ty, formula}) do
    with {:ok, sort} <- bind(book, ty) do
      walk_formula(book, data, Map.put(env, x, sort), formula)
    end
  end

  defp walk_formula(book, data, env, {:always, prop}), do: walk_prop(book, data, env, prop)
  defp walk_formula(book, data, env, {:eventually, prop}), do: walk_prop(book, data, env, prop)

  defp walk_formula(book, data, env, {:leads_to, p, q}) do
    with :ok <- walk_prop(book, data, env, p), do: walk_prop(book, data, env, q)
  end

  defp walk_formula(_book, _data, _env, _other) do
    {:error, "a family formula names opened, held, or resolved"}
  end

  defp walk_prop(_book, _data, _env, true), do: :ok
  defp walk_prop(_book, _data, _env, false), do: :ok

  defp walk_prop(book, data, env, {:not, p}), do: walk_prop(book, data, env, p)

  defp walk_prop(book, data, env, {:and, p, q}) do
    with :ok <- walk_prop(book, data, env, p), do: walk_prop(book, data, env, q)
  end

  defp walk_prop(book, data, env, {:or, p, q}) do
    with :ok <- walk_prop(book, data, env, p), do: walk_prop(book, data, env, q)
  end

  defp walk_prop(book, data, env, {:imp, p, q}) do
    with :ok <- walk_prop(book, data, env, p), do: walk_prop(book, data, env, q)
  end

  defp walk_prop(book, data, env, {atom, key, kind}) when atom in [:opened, :held, :resolved] do
    with :ok <- expect_key(book, env, atom, key), do: expect_ctor(data, kind)
  end

  defp walk_prop(_book, _data, _env, _other) do
    {:error, "a family formula names opened, held, or resolved"}
  end

  defp expect_key(book, env, atom, key) do
    case Map.get(env, key) do
      :key ->
        :ok

      :value ->
        {:error, "#{atom} expects a key"}

      nil ->
        if run?(book, key) do
          {:error, @run_msg}
        else
          {:error, "unbound key #{key}"}
        end
    end
  end

  defp expect_ctor(%{name: type_name, ctors: ctors}, kind) do
    if Enum.any?(ctors, &(&1.name == kind)) do
      :ok
    else
      {:error, "#{kind} is not a constructor of #{type_name}"}
    end
  end

  defp run?(book, name) do
    Enum.any?(book, fn d ->
      Map.get(d, :name) == name and Map.get(d, :mode) == :run and term?(d)
    end)
  end

  defp term?(%{kind: kind})
       when kind in [
              :data,
              :session,
              :conform,
              :place,
              :scheme,
              :move,
              :endpoint,
              :read,
              :meet,
              :temporal,
              :family,
              :talk,
              :choreography,
              :repr,
              :seat,
              :link,
              :relay,
              :import,
              :param
            ],
       do: false

  defp term?(_), do: true
end
