defmodule Muro.FsmFamilyTest do
  use ExUnit.Case, async: false

  alias Muro.Family.Graph

  @moduletag timeout: 180_000

  @path "examples/keyed-slots.muro"

  setup do
    on_exit(fn ->
      for {mod, _} <- :code.all_loaded(),
          name = Atom.to_string(mod),
          String.starts_with?(name, "Elixir.FsmFam") do
        :code.purge(mod)
        :code.delete(mod)
      end
    end)

    :ok
  end

  test "the production trace holds, opens, and releases" do
    {disp, parent, _src} = compile!()
    search = search!()
    assert length(search.states) == 171_649
    assert search.transitions == 729_184

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:open, 2, state} = disp.arrive(state, "b", :init, 0)
    assert {:ok, [{1, "a", :signal}], state} = disp.resolved(state, 0)
    assert {:ok, [], state} = disp.resolved(state, 1)
    assert {:ok, [], _state} = disp.resolved(state, 2)

    trace = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:arrive, "b", :init, 0},
      {:resolved, 0},
      {:resolved, 1},
      {:resolved, 2}
    ]

    assert :ok = disp.check_trace(trace)

    lockstep!(search, [
      {:arrive, "a", :init, 0, :open, 0},
      {:arrive, "a", :signal, 1, :held, 1},
      {:arrive, "b", :init, 0, :open, 2},
      {:resolved, 0, [{1, "a", :signal}]},
      {:resolved, 1, []},
      {:resolved, 2, []}
    ])

    server = Module.concat(parent, ServerWait)
    task = Module.concat(parent, TaskWork)
    assert function_exported?(server, :init, 0)
    assert function_exported?(server, :down, 1)
    assert function_exported?(task, :send, 2)
    refute function_exported?(disp, :send, 2)
    assert {:recv, {:data, "Report", []}} = server.expected(server.init())
  end

  test "resolved of an unknown id is an error and does not raise" do
    {disp, _parent, _src} = compile!()
    state = disp.new()

    assert {:error, {:unknown, 0}} = disp.resolved(state, 0)
    assert {:error, {:unknown, 99}} = disp.resolved(state, 99)
    assert {:error, {0, {:unknown, 4}}} = disp.check_trace([{:resolved, 4}])
    assert {:error, {:state, :nope}} = disp.resolved(:nope, 0)
    assert {:error, {:state, :nope}} = disp.arrive(:nope, "a", :init, 0)
    assert {:error, {:trace, :nope}} = disp.check_trace(:nope)

    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:error, {:held, 1}} = disp.resolved(state, 1)
    assert {:error, {:kind, :nope}} = disp.arrive(state, "a", :nope, 3)
    assert {:error, {:kind, "init"}} = disp.arrive(state, "a", "init", 3)
    assert {:error, {:index, -1}} = disp.arrive(state, "a", :signal, -1)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(state, "a", :signal, 0)
    assert {:ok, [{1, "a", :signal}], state} = disp.resolved(state, 0)
    assert {:error, {:resolved, 0}} = disp.resolved(state, 0)
  end

  test "a later signal opens before its init arrives, and an earlier signal blocks the next" do
    {disp, _parent, _src} = compile!()
    search = search!()
    g = search.g

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :signal, 1)
    assert {:open, 1, _state} = disp.arrive(state, "a", :init, 0)

    {_assigned, gst} =
      lockstep!(search, [
        {:arrive, "a", :signal, 1, :open, 0},
        {:arrive, "a", :init, 0, :open, 1}
      ])

    signal = Enum.find(g.instances, &(&1.key == "a" and &1.kind == "signal" and &1.index == 1))
    init = Enum.find(g.instances, &(&1.key == "a" and &1.kind == "init"))
    assert match?({:run, _, _, _}, Graph.phase(gst, signal.id))
    assert match?({:run, _, _, _}, Graph.phase(gst, init.id))
    refute Graph.known_at_open?(gst, signal.id, init.id)

    assert Graph.holds?(
             g,
             {:imp, {:opened, "a", "signal"}, {:resolved, "a", "init"}},
             gst
           )

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:held, 2, state} = disp.arrive(state, "a", :signal, 2)
    assert {:ok, [{1, "a", :signal}], state} = disp.resolved(state, 0)
    assert {:held, _} = hold_of(disp, state, 2)
    assert {:ok, [{2, "a", :signal}], _state} = disp.resolved(state, 1)

    lockstep!(search, [
      {:arrive, "a", :init, 0, :open, 0},
      {:arrive, "a", :signal, 1, :held, 1},
      {:arrive, "a", :signal, 2, :held, 2},
      {:resolved, 0, [{1, "a", :signal}]},
      {:resolved, 1, [{2, "a", :signal}]}
    ])
  end

  test "a second init opens at once and the signal waits for both" do
    {disp, _parent, _src} = compile!()
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:open, 1, state} = disp.arrive(state, "a", :init, 1)
    assert {:held, 2, state} = disp.arrive(state, "a", :signal, 2)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert {:held, _} = hold_of(disp, state, 2)
    assert {:ok, [{2, "a", :signal}], _state} = disp.resolved(state, 1)

    search = search!(two_inits())

    lockstep!(search, [
      {:arrive, "a", :init, 0, :open, 0},
      {:arrive, "a", :init, 1, :open, 1},
      {:arrive, "a", :signal, 2, :held, 2},
      {:resolved, 0, []},
      {:resolved, 1, [{2, "a", :signal}]}
    ])
  end

  test "every dispatcher-accepted sequence over the script is a run of the family graph" do
    {disp, _parent, _src} = compile!()
    search = search!()
    assert length(search.states) == 171_649
    assert search.transitions == 729_184

    n =
      walk(
        disp,
        search,
        disp.new(),
        search.g.start,
        search.g.instances,
        %{},
        MapSet.new(),
        []
      )

    assert n > 1
  end

  defp hold_of(disp, state, id) do
    case disp.resolved(state, id) do
      {:error, {:held, ^id}} -> {:held, id}
      other -> flunk("expected the instance to stay held, got #{inspect(other)}")
    end
  end

  defp walk(disp, search, dst, gst, remaining, assigned, resolved, trace) do
    assert {:error, {:unknown, _}} = disp.resolved(dst, -1)

    arrived =
      Enum.reduce(remaining, 0, fn inst, acc ->
        kind = String.to_atom(inst.kind)

        case disp.arrive(dst, inst.key, kind, inst.index) do
          {phase, id, dst2} when phase in [:open, :held] ->
            tag = if phase == :open, do: {:open, inst.id}, else: {:hold, inst.id}

            case step_to(search, gst, tag) do
              {:ok, gst2} ->
                left = Enum.reject(remaining, &(&1.id == inst.id))
                step = {:arrive, inst.key, kind, inst.index, phase}

                acc +
                  walk(
                    disp,
                    search,
                    dst2,
                    gst2,
                    left,
                    Map.put(assigned, id, inst),
                    resolved,
                    [step | trace]
                  )

              {:error, tags} ->
                flunk(mismatch(trace, tag, tags))
            end

          other ->
            flunk("dispatcher refused #{inspect(inst)} after #{show(trace)}: #{inspect(other)}")
        end
      end)

    finished =
      Enum.reduce(assigned, 0, fn {id, inst}, acc ->
        if MapSet.member?(resolved, id) do
          acc
        else
          case disp.resolved(dst, id) do
            {:error, _} ->
              case Graph.phase(gst, inst.id) do
                :held ->
                  acc

                other ->
                  flunk(
                    "dispatcher refused a running #{who(inst)} after #{show(trace)}, graph phase #{inspect(other)}"
                  )
              end

            {:ok, released, dst2} ->
              case realize(search, gst, inst.id) do
                {:ok, gst2, opened} ->
                  got = MapSet.new(released, &graph_id(assigned, &1))

                  if got == MapSet.new(opened) do
                    step = {:resolved, id, released}

                    acc +
                      walk(
                        disp,
                        search,
                        dst2,
                        gst2,
                        remaining,
                        assigned,
                        MapSet.put(resolved, id),
                        [step | trace]
                      )
                  else
                    flunk(
                      "release mismatch after #{show(trace)}: dispatcher #{inspect(released)} graph #{inspect(opened)}"
                    )
                  end

                :error ->
                  flunk(
                    "accepted resolve of #{who(inst)} is not a graph run after #{show(trace)}"
                  )
              end
          end
        end
      end)

    if arrived + finished == 0, do: 1, else: arrived + finished
  end

  defp lockstep!(search, trace) do
    Enum.reduce(trace, {%{}, search.g.start}, fn step, {assigned, gst} ->
      case step do
        {:arrive, key, kind, index, phase, id} ->
          inst = find_inst!(search.g, key, kind, index)
          tag = if phase == :open, do: {:open, inst.id}, else: {:hold, inst.id}

          case step_to(search, gst, tag) do
            {:ok, gst} -> {Map.put(assigned, id, inst), gst}
            {:error, tags} -> flunk(mismatch(trace, tag, tags))
          end

        {:resolved, id, released} ->
          inst = Map.fetch!(assigned, id)

          case realize(search, gst, inst.id) do
            {:ok, gst, opened} ->
              got = MapSet.new(released, &graph_id(assigned, &1))

              assert MapSet.new(opened) == got,
                     "release mismatch: dispatcher #{inspect(released)} graph #{inspect(opened)}"

              {assigned, gst}

            :error ->
              flunk("resolve of #{who(inst)} is not a graph run")
          end
      end
    end)
  end

  defp find_inst!(g, key, kind, index) do
    kind = Atom.to_string(kind)

    Enum.find(g.instances, &(&1.key == key and &1.kind == kind and &1.index == index)) ||
      flunk("script has no #{key} #{kind} #{index}")
  end

  defp graph_id(assigned, {id, key, kind}) do
    inst = Map.fetch!(assigned, id)
    assert inst.key == key
    assert inst.kind == Atom.to_string(kind)
    inst.id
  end

  defp realize(search, state, gid) do
    case bfs(search, gid, MapSet.new(), [state]) do
      nil ->
        :error

      resolved ->
        ids = held_opens(search, resolved)

        case apply_opens(search, resolved, Enum.sort(ids)) do
          {:ok, dest} -> {:ok, dest, ids}
          :error -> :error
        end
    end
  end

  defp bfs(_search, _gid, _seen, []), do: nil

  defp bfs(search, gid, seen, [state | rest]) do
    if MapSet.member?(seen, state) do
      bfs(search, gid, seen, rest)
    else
      steps = steps_of(search, state)

      case resolving(steps, gid) do
        {_tag, dest} ->
          dest

        nil ->
          more =
            for {tag, dest} <- steps,
                match?({:meet, ^gid, _}, tag) or tag == {:retry, gid},
                do: dest

          bfs(search, gid, MapSet.put(seen, state), rest ++ more)
      end
    end
  end

  defp resolving(steps, gid) do
    Enum.find(steps, fn {tag, _} -> tag == {:resolve, gid} end) ||
      Enum.find(steps, fn {tag, _} -> tag == {:give_up, gid} end)
  end

  defp held_opens(search, state) do
    steps = steps_of(search, state)

    for inst <- search.g.instances,
        Graph.phase(state, inst.id) == :held,
        Enum.any?(steps, fn {tag, _} -> tag == {:open, inst.id} end),
        do: inst.id
  end

  defp apply_opens(_search, state, []), do: {:ok, state}

  defp apply_opens(search, state, [id | rest]) do
    case step_to(search, state, {:open, id}) do
      {:ok, state} -> apply_opens(search, state, rest)
      {:error, _} -> :error
    end
  end

  defp step_to(search, state, tag) do
    case Enum.find(steps_of(search, state), fn {t, _} -> t == tag end) do
      {_, dest} -> {:ok, dest}
      nil -> {:error, steps_of(search, state) |> Enum.map(&elem(&1, 0))}
    end
  end

  defp steps_of(search, state) do
    case Map.fetch(search.edges, state) do
      {:ok, steps} -> steps
      :error -> Graph.edges(search.g, state)
    end
  end

  defp mismatch(trace, tag, tags) do
    "graph has no #{inspect(tag)} after #{show(trace)}; edges #{inspect(tags)}"
  end

  defp show(trace) when is_list(trace), do: inspect(Enum.reverse(trace))

  defp who(inst), do: "#{inst.key} #{inst.kind} #{inst.index}"

  defp two_inits do
    [
      %{id: 0, key: "a", kind: "init", index: 0},
      %{id: 1, key: "a", kind: "init", index: 1},
      %{id: 2, key: "a", kind: "signal", index: 2}
    ]
  end

  defp search!(instances \\ nil) do
    src = File.read!(@path)
    assert {:ok, book} = Muro.Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))
    opts = if instances, do: [instances: instances], else: []
    assert {:ok, search} = Graph.prepare(book, family, opts)
    search
  end

  defp compile! do
    parent = Module.concat(["FsmFam#{System.unique_integer([:positive])}"])
    assert {:ok, src} = Muro.emit_fsm(@path, parent)
    assert src =~ "defmodule Slots do"
    assert src =~ "def new"
    assert src =~ "def arrive"
    assert src =~ "def resolved"
    assert src =~ "def check_trace"
    refute src =~ "GenServer"
    refute src =~ "Muro."
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(src) end)

    warnings =
      Enum.filter(diags, &(match?(%{severity: :warning}, &1) or match?({:warning, _}, &1)))

    assert warnings == [], inspect(warnings, limit: 20)
    assert parent in Enum.map(mods, &elem(&1, 0))
    {Module.concat(parent, Slots), parent, src}
  end
end
