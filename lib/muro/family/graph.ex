defmodule Muro.Family.Graph do
  @moduledoc """
  The composed graph of one keyed family, on a fixed script.

  Each instance runs the meeting graph `Muro.Temporal` already builds.
  A step arrives at one instance, opens one that the rule allows, takes
  one meeting step, retries that meeting, gives it up, or resolves it.
  Instances of one key may arrive in any order. An earlier creation
  index can arrive after a later one has opened.

  `always`, `eventually`, and `leads_to` are decided here, on the
  same search. Nothing in this module is an Agda proof.

  A count of reachable states is a model hypothesis, not
  data-independence. The model is one retry and the fixed script.
  """

  alias Muro.Temporal.Graph, as: Meet

  # One rerun after the first attempt. The next death gives up.
  # With the fixed script in `instances/2`, this bound is the model.
  # A "holds in N states" count is a model hypothesis, not
  # data-independence.
  @bound 1

  @doc false
  def bound, do: @bound

  @doc """
  `{:ok, search}` with the reachable states, the breadth-first parents,
  and the successor-table size. `{:error, message}` when the meeting
  has no compiled graph, or when that meeting is stuck.

  The meeting is the one `Muro.Temporal.prepare/3` returns, so `NoStuck`
  runs once on the meeting before any family state is built. A may-fail
  death or drop is a step, and a bad view that still has one is not
  stuck. A meeting the checker has accepted stays accepted. The family
  counts are the script, and this pass does not change them.

  The counts are a model hypothesis, not data-independence.
  """
  def prepare(book, family, opts \\ []) when is_list(book) do
    # Noted before the cache, so a caller can see that prepare ran
    # even when the suite reuses a search it already built.
    Muro.Explore.note(:family, family.name)

    with {:ok, meet} <- fetch_meet(book, family.meeting),
         {:ok, %{g: mg}} <- Muro.Temporal.prepare(book, meet.name, :ok) do
      instances = Keyword.get(opts, :instances) || instances(book, family)
      rules = Map.new(family.rules, &{&1.ctor, &1.hold})

      remember({mg, instances, rules, family.name}, fn ->
        compose(family, mg, instances, rules)
      end)
    end
  end

  defp compose(family, mg, instances, rules) do
    {server, task} = roles(mg)

    g = %{
      family: family.name,
      meet: mg,
      instances: instances,
      by_id: Map.new(instances, &{&1.id, &1}),
      rules: rules,
      keys: instances |> Enum.map(& &1.key) |> Enum.uniq(),
      server: server,
      task: task,
      init: Meet.init(mg),
      start: Tuple.duplicate(:absent, length(instances))
    }

    {states, parents, transitions, edges} = reachable(g)

    {:ok, %{g: g, states: states, parents: parents, transitions: transitions, edges: edges}}
  end

  # The worked script is about 171649 states. The suite sets
  # `:family_graph_cache` and reuses one search. A check outside the
  # suite builds that graph once per family and does not keep it.
  defp remember(key, fun) do
    if Application.get_env(:muro, :family_graph_cache, false) do
      case :persistent_term.get({__MODULE__, key}, :miss) do
        :miss ->
          result = fun.()
          if match?({:ok, _}, result), do: :persistent_term.put({__MODULE__, key}, result)
          result

        result ->
          result
      end
    else
      fun.()
    end
  end

  @doc false
  def instances(book, %{key: key, rules: rules}) do
    data = Enum.find(book, &(&1[:kind] == :data and &1.name == key))
    ctors = Enum.map(data.ctors, & &1.name)
    hold = Map.new(rules, &{&1.ctor, &1.hold})

    script_a =
      Enum.flat_map(ctors, fn ctor ->
        if hold[ctor] == :earlier, do: [ctor, ctor], else: [ctor]
      end)

    script_b = [hd(ctors)]

    [tagged("a", script_a), tagged("b", script_b)]
    |> List.flatten()
    |> Enum.with_index()
    |> Enum.map(fn {{key, kind, index}, id} ->
      %{id: id, key: key, kind: kind, index: index}
    end)
  end

  defp tagged(key, script) do
    Enum.with_index(script, fn kind, index -> {key, kind, index} end)
  end

  @doc """
  `{:ok, states, transitions}` when every instance of the formula holds.
  `{:error, message}` is the breadth-first trace of the first `always`
  that does not, or the lasso of the first `eventually` or `leads_to`
  that does not. A `forall` whose type is not `key` is
  `forall over <name> is not a key`.

  `states` is a model hypothesis, not data-independence. The successor
  table this count sums is the one liveness prunes. Keeping it does
  not add a state or a transition.
  """
  def decide(%{g: g, states: states, transitions: m} = search, formula) do
    case formulas(g, formula) do
      {:error, msg} ->
        {:error, msg}

      props ->
        case Enum.find_value(props, &verdict(search, &1)) do
          nil -> {:ok, length(states), m}
          {:no, msg} -> {:error, msg}
        end
    end
  end

  @doc false
  def holds?(g, prop, state) do
    holds(g, state, prop)
  end

  @doc false
  def phase(state, id), do: elem(state, id)

  @doc false
  def known_at_open?(state, id, other) do
    case elem(state, id) do
      {:run, _, _, mask} -> Bitwise.band(mask, bit(other)) != 0
      _ -> false
    end
  end

  # A held kind is running only when every earlier instance of its key
  # that was already known at that opening is resolved. A kind that is
  # never held has no such obligation.
  @doc false
  def respects?(g, state) do
    Enum.all?(g.instances, fn inst ->
      case phase(state, inst.id) do
        {:run, _, _, mask} ->
          g.rules[inst.kind] == :never or earlier_clear?(g, state, inst, mask)

        _ ->
          true
      end
    end)
  end

  defp earlier_clear?(g, state, inst, mask) do
    Enum.all?(g.instances, fn other ->
      other.key != inst.key or other.index >= inst.index or
        not unresolved?(phase(state, other.id)) or
        Bitwise.band(mask, bit(other.id)) == 0
    end)
  end

  defp verdict(search, {:always, prop}) do
    %{g: g, states: states, parents: parents} = search

    case Enum.find(states, fn state -> not holds(g, state, prop) end) do
      nil -> nil
      state -> {:no, safety_msg(g, prop, trace(parents, state), state)}
    end
  end

  # The same prune as `Muro.Temporal.prune`: a state leaves the region
  # when no successor remains in it, and what remains can reach a cycle
  # there. Destinations are already unwrapped. A family state can be a
  # pair whose first cell is an atom, which `Temporal.prune` would read
  # as an edge tag.
  defp verdict(%{g: g, states: states} = search, {:eventually, prop}) do
    region = Enum.filter(states, fn state -> not holds(g, state, prop) end)
    z = prune(search, region)

    if MapSet.member?(MapSet.new(z), g.start) do
      {stem, loop} = lasso(search, z, g.start)
      {:no, live_msg(g, {:eventually, prop}, [], stem, loop)}
    else
      nil
    end
  end

  defp verdict(%{g: g, states: states, parents: parents} = search, {:leads_to, p, q}) do
    if Enum.any?(states, &holds(g, &1, p)) do
      region = Enum.filter(states, fn state -> not holds(g, state, q) end)
      z = prune(search, region)
      zset = MapSet.new(z)

      case Enum.find(states, fn state -> holds(g, state, p) and MapSet.member?(zset, state) end) do
        nil ->
          nil

        state ->
          {stem, loop} = lasso(search, z, state)
          {:no, live_msg(g, {:leads_to, p, q}, trace(parents, state), stem, loop)}
      end
    else
      nil
    end
  end

  defp prune(%{edges: edges}, region) when is_map(edges), do: prune_region(region, edges)

  defp prune(%{g: g, states: states}, region) do
    prune_region(region, Map.new(states, fn state -> {state, edges(g, state)} end))
  end

  defp prune_region(nodes, succ) do
    member = MapSet.new(nodes)

    {degree, preds} =
      Enum.reduce(nodes, {%{}, %{}}, fn node, {degree, preds} ->
        outs =
          succ
          |> Map.get(node, [])
          |> Enum.map(fn {_tag, dest} -> dest end)
          |> Enum.filter(&MapSet.member?(member, &1))

        degree = Map.put(degree, node, length(outs))

        preds =
          Enum.reduce(outs, preds, fn target, preds ->
            Map.update(preds, target, [node], &[node | &1])
          end)

        {degree, preds}
      end)

    queue = Enum.filter(nodes, &(Map.get(degree, &1, 0) == 0))
    alive = drop_zeros(queue, [], degree, preds, member)
    Enum.filter(nodes, &MapSet.member?(alive, &1))
  end

  defp drop_zeros([], [], _degree, _preds, alive), do: alive

  defp drop_zeros([], back, degree, preds, alive) do
    drop_zeros(:lists.reverse(back), [], degree, preds, alive)
  end

  defp drop_zeros([node | rest], back, degree, preds, alive) do
    if MapSet.member?(alive, node) do
      alive = MapSet.delete(alive, node)

      {degree, back} =
        Enum.reduce(Map.get(preds, node, []), {degree, back}, fn pred, {degree, back} ->
          if MapSet.member?(alive, pred) do
            left = Map.get(degree, pred, 0) - 1
            degree = Map.put(degree, pred, left)
            back = if left == 0, do: [pred | back], else: back
            {degree, back}
          else
            {degree, back}
          end
        end)

      drop_zeros(rest, back, degree, preds, alive)
    else
      drop_zeros(rest, back, degree, preds, alive)
    end
  end

  # `{stem, loop}` are steps `{tag, src, dest}`. The first edge that
  # stays in the region is the one the meeting checker would take.
  # `leads_to` puts the breadth-first parent trace in front of that pair.
  defp lasso(%{edges: edges}, z, state) when is_map(edges) do
    walk(edges, MapSet.new(z), state, MapSet.new(), state, [])
  end

  defp lasso(%{g: g}, z, state) do
    edges = Map.new(z, fn node -> {node, edges(g, node)} end)
    walk(edges, MapSet.new(z), state, MapSet.new(), state, [])
  end

  defp walk(edges, zset, state, seen, origin, steps) do
    if MapSet.member?(seen, state) do
      cut(state, origin, :lists.reverse(steps))
    else
      case first_out(edges, zset, state) do
        {tag, dest} ->
          walk(edges, zset, dest, MapSet.put(seen, state), origin, [{tag, state, dest} | steps])

        nil ->
          {[], []}
      end
    end
  end

  defp first_out(edges, zset, state) do
    Enum.find(Map.get(edges, state, []), fn {_tag, dest} -> MapSet.member?(zset, dest) end)
  end

  defp cut(target, origin, steps) when target == origin, do: {[], steps}
  defp cut(target, _origin, steps), do: split_at(target, steps, [])

  defp split_at(_target, [], acc), do: {Enum.reverse(acc), []}

  defp split_at(target, [{_tag, _src, dest} = step | rest], acc) when dest == target do
    {Enum.reverse([step | acc]), rest}
  end

  defp split_at(target, [step | rest], acc), do: split_at(target, rest, [step | acc])

  defp formulas(g, formula) do
    case peel(formula, []) do
      {:error, _} = err ->
        err

      {:ok, {binders, {:always, prop}}} ->
        tag_all(:always, instantiate(prop, binders, g.keys))

      {:ok, {binders, {:eventually, prop}}} ->
        tag_all(:eventually, instantiate(prop, binders, g.keys))

      {:ok, {binders, {:leads_to, p, q}}} ->
        instantiate_to(p, q, binders, g.keys)

      {:ok, _} ->
        {:error, "a family formula names opened, held, or resolved"}
    end
  end

  defp tag_all(kind, props) when is_list(props), do: Enum.map(props, &{kind, &1})

  defp instantiate_to(p, q, [], _keys), do: [{:leads_to, p, q}]

  defp instantiate_to(p, q, [{:key, var} | rest], keys) do
    Enum.flat_map(keys, fn key ->
      instantiate_to(subst(p, var, key), subst(q, var, key), rest, keys)
    end)
  end

  defp peel({:forall, x, {:dat, "key", []}, body}, acc), do: peel(body, [{:key, x} | acc])

  defp peel({:forall, _x, ty, _body}, _acc) do
    {:error, "forall over #{forall_ty(ty)} is not a key"}
  end

  defp peel(body, acc), do: {:ok, {Enum.reverse(acc), body}}

  defp forall_ty(:bit), do: "Bit"
  defp forall_ty(:nat), do: "Nat"
  defp forall_ty(:unit), do: "Unit"
  defp forall_ty({:dat, name, _}), do: name
  defp forall_ty({:vec, _, _}), do: "Vec"
  defp forall_ty({:pair, _, _}), do: "a pair"
  defp forall_ty({:rec, _}), do: "a record"
  defp forall_ty(other), do: inspect(other)

  defp instantiate(prop, [], _keys), do: [prop]

  defp instantiate(prop, [{:key, var} | rest], keys) do
    Enum.flat_map(keys, fn key ->
      instantiate(subst(prop, var, key), rest, keys)
    end)
  end

  defp subst({:not, p}, var, key), do: {:not, subst(p, var, key)}
  defp subst({:and, p, q}, var, key), do: {:and, subst(p, var, key), subst(q, var, key)}
  defp subst({:or, p, q}, var, key), do: {:or, subst(p, var, key), subst(q, var, key)}
  defp subst({:imp, p, q}, var, key), do: {:imp, subst(p, var, key), subst(q, var, key)}

  defp subst({atom, name, kind}, var, key) when atom in [:opened, :held, :resolved] do
    {atom, if(name == var, do: key, else: name), kind}
  end

  defp subst(other, _var, _key), do: other

  defp holds(_g, _state, true), do: true
  defp holds(_g, _state, false), do: false
  defp holds(g, state, {:not, p}), do: not holds(g, state, p)
  defp holds(g, state, {:and, p, q}), do: holds(g, state, p) and holds(g, state, q)
  defp holds(g, state, {:or, p, q}), do: holds(g, state, p) or holds(g, state, q)
  defp holds(g, state, {:imp, p, q}), do: not holds(g, state, p) or holds(g, state, q)

  defp holds(g, state, {:opened, key, kind}) do
    Enum.any?(g.instances, fn inst ->
      inst.key == key and inst.kind == kind and running?(phase(state, inst.id))
    end)
  end

  defp holds(g, state, {:held, key, kind}) do
    Enum.any?(g.instances, fn inst ->
      inst.key == key and inst.kind == kind and phase(state, inst.id) == :held
    end)
  end

  # A known instance counts, unless some other running instance of the
  # same key opened before this one was known. That late arrival does
  # not falsify `resolved` while the earlier opening is still running.
  # When nothing of the key is running, every known instance counts.
  defp holds(g, state, {:resolved, key, kind}) do
    runners = runners(g, state, key)

    Enum.all?(g.instances, fn inst ->
      inst.key != key or inst.kind != kind or not counts?(state, inst, runners) or
        resolved?(phase(state, inst.id))
    end)
  end

  defp runners(g, state, key) do
    Enum.filter(g.instances, fn inst ->
      inst.key == key and running?(phase(state, inst.id))
    end)
  end

  defp counts?(state, inst, runners) do
    phase = phase(state, inst.id)

    known?(phase) and
      not Enum.any?(runners, fn other ->
        other.id != inst.id and not known_at_open?(state, other.id, inst.id)
      end)
  end

  # `@bound` is one retry. `instances/2` is the fixed script. The
  # length of this search is a model hypothesis, not data-independence.
  defp reachable(g) do
    drain(g, [g.start], [], MapSet.new([g.start]), %{}, [], 0, [])
  end

  defp drain(_g, [], [], _seen, parents, acc, trans, edge_acc) do
    {Enum.reverse(acc), parents, trans, Map.new(edge_acc)}
  end

  defp drain(g, [], back, seen, parents, acc, trans, edge_acc) do
    drain(g, :lists.reverse(back), [], seen, parents, acc, trans, edge_acc)
  end

  defp drain(g, [state | front], back, seen, parents, acc, trans, edge_acc) do
    steps = edges(g, state)

    {back, seen, parents} =
      Enum.reduce(steps, {back, seen, parents}, fn {tag, dest}, {back, seen, parents} ->
        if tag == :stay or MapSet.member?(seen, dest) do
          {back, seen, parents}
        else
          {[dest | back], MapSet.put(seen, dest), Map.put(parents, dest, {tag, state})}
        end
      end)

    drain(
      g,
      front,
      back,
      seen,
      parents,
      [state | acc],
      trans + length(steps),
      [{state, steps} | edge_acc]
    )
  end

  @doc false
  def edges(g, state) do
    case real_steps(g, state) do
      [] -> [{:stay, state}]
      steps -> steps
    end
  end

  defp real_steps(g, state) do
    Enum.flat_map(g.instances, &instance_steps(g, state, &1))
  end

  defp instance_steps(g, state, inst) do
    case phase(state, inst.id) do
      :absent ->
        [arrival(g, state, inst)]

      :held ->
        if opens?(g, state, inst) do
          [
            {{:open, inst.id},
             put_phase(state, inst.id, {:run, g.init, 0, mask(g, state, inst.id)})}
          ]
        else
          []
        end

      {:run, conf, attempt, known} ->
        meet_steps(g, state, inst, conf, attempt, known) ++
          retry_step(g, state, inst, conf, attempt, known) ++
          resolve_step(g, state, inst, conf)

      _ ->
        []
    end
  end

  defp arrival(g, state, inst) do
    if opens?(g, state, inst) do
      {{:open, inst.id}, put_phase(state, inst.id, {:run, g.init, 0, mask(g, state, inst.id)})}
    else
      {{:hold, inst.id}, put_phase(state, inst.id, :held)}
    end
  end

  # `never` opens on arrival, including a second init of a key whose
  # first init is still running. `earlier` opens when every earlier
  # known instance of the key is resolved. An instance that has not
  # arrived is not unresolved.
  defp opens?(g, state, inst) do
    g.rules[inst.kind] == :never or
      Enum.all?(g.instances, fn other ->
        other.key != inst.key or other.index >= inst.index or
          not unresolved?(phase(state, other.id))
      end)
  end

  defp meet_steps(g, state, inst, conf, attempt, known) do
    Enum.map(Meet.steps_of(g.meet, conf), fn {who, dest} ->
      {{:meet, inst.id, who}, put_phase(state, inst.id, {:run, dest, attempt, known})}
    end)
  end

  # A retry restarts the meeting while the task has stopped and the
  # server has not reached `done` or `stop`. One rerun, then give-up.
  # Give-up is resolved for the atom and is not delivered. A server
  # already at `stop` stays in this meeting: the instance is unresolved,
  # and a later signal of its key stays held.
  defp retry_step(g, state, inst, conf, attempt, known) do
    cond do
      not task_dead?(g, conf) ->
        []

      server_terminal?(g, conf) ->
        []

      attempt < @bound ->
        [{{:retry, inst.id}, put_phase(state, inst.id, {:run, g.init, attempt + 1, known})}]

      true ->
        [{{:give_up, inst.id}, put_phase(state, inst.id, :gave_up)}]
    end
  end

  defp resolve_step(g, state, inst, conf) do
    if server_done?(g, conf) do
      [{{:resolve, inst.id}, put_phase(state, inst.id, :resolved)}]
    else
      []
    end
  end

  defp unresolved?({:run, _, _, _}), do: true
  defp unresolved?(:held), do: true
  defp unresolved?(_), do: false

  defp running?({:run, _, _, _}), do: true
  defp running?(_), do: false

  defp resolved?(:resolved), do: true
  defp resolved?(:gave_up), do: true
  defp resolved?(_), do: false

  defp known?(:absent), do: false
  defp known?(_), do: true

  defp mask(g, state, self) do
    Enum.reduce(g.instances, bit(self), fn inst, acc ->
      if known?(phase(state, inst.id)), do: Bitwise.bor(acc, bit(inst.id)), else: acc
    end)
  end

  defp bit(id), do: Bitwise.bsl(1, id)

  defp put_phase(state, id, phase), do: put_elem(state, id, phase)

  # The server is the party that is not marked. The left party is the
  # server when the mark does not choose. Resolved is that party at
  # `done` with both queues empty. Giving up is resolved without that.
  defp server_done?(g, conf) do
    queues_empty?(conf) and block_kind(g, g.server, conf) == :done
  end

  defp server_terminal?(g, conf) do
    block_kind(g, g.server, conf) in [:done, :stop]
  end

  defp task_dead?(%{task: nil}, _conf), do: false
  defp task_dead?(g, conf), do: ptr(conf, g.task) == :dead

  defp queues_empty?({_, _, [], [], _, _}), do: true
  defp queues_empty?(_), do: false

  defp block_kind(g, side, conf) do
    code = if side == :l, do: g.meet.code_l, else: g.meet.code_r

    case ptr(conf, side) do
      :dead -> :dead
      i -> block_k(Enum.at(code, i))
    end
  end

  defp block_k(%{k: k}), do: k
  defp block_k(_), do: nil

  defp ptr(conf, :l), do: elem(conf, 0)
  defp ptr(conf, :r), do: elem(conf, 1)

  defp roles(mg) do
    may_l = Map.get(mg, :may_l, false)
    may_r = Map.get(mg, :may_r, false)

    cond do
      may_r and not may_l -> {:l, :r}
      may_l and not may_r -> {:r, :l}
      may_l and may_r -> {:l, :r}
      true -> {:l, nil}
    end
  end

  defp fetch_meet(book, name) do
    case Enum.find(book, &match?(%{kind: :meet, name: ^name}, &1)) do
      nil -> {:error, "unknown meeting #{name}"}
      meet -> {:ok, meet}
    end
  end

  defp trace(parents, state), do: trace(parents, state, [])

  defp trace(parents, state, acc) do
    case Map.get(parents, state) do
      nil -> acc
      {tag, parent} -> trace(parents, parent, [{tag, parent, state} | acc])
    end
  end

  defp safety_msg(g, prop, steps, state) do
    live_or_safe(g, {:always, prop}, steps, state)
  end

  # The prefix is the path to the cycle. An empty stem is not copied
  # onto that path. The cycle is what follows `then forever`.
  defp live_msg(g, formula, to_c, stem, loop) do
    prefix = to_c ++ stem
    body = pp_form(formula)
    forever = labels(g, loop)

    if prefix == [] do
      "#{body} fails in #{g.family}; then forever: #{forever}"
    else
      "#{body} fails in #{g.family} after #{labels(g, prefix)}; then forever: #{forever}"
    end
  end

  defp live_or_safe(g, {:always, prop}, steps, state) do
    body = pp_form({:always, prop})

    if steps == [] do
      "#{body} fails in #{g.family}: #{dump(g, state)}"
    else
      "#{body} fails in #{g.family} after #{labels(g, steps)}: #{dump(g, state)}"
    end
  end

  defp pp_form({:always, prop}), do: "always (#{pp(prop)})"
  defp pp_form({:eventually, prop}), do: "eventually (#{pp(prop)})"
  defp pp_form({:leads_to, p, q}), do: "(#{pp(p)}) leads_to (#{pp(q)})"

  defp labels(g, steps), do: Enum.map_join(steps, ", ", &step_label(g, &1))

  defp step_label(g, {tag, src, dest}), do: step_name(g, src, dest, tag)

  defp step_name(g, _src, _dest, {:open, id}), do: "#{who(g, id)} opens"
  defp step_name(g, _src, _dest, {:hold, id}), do: "#{who(g, id)} held"
  defp step_name(g, _src, _dest, {:resolve, id}), do: "#{who(g, id)} resolves"
  defp step_name(g, _src, _dest, {:retry, id}), do: "#{who(g, id)} retries"
  defp step_name(g, _src, _dest, {:give_up, id}), do: "#{who(g, id)} gives up"
  defp step_name(_g, _src, _dest, :stay), do: "the family has finished"

  defp step_name(g, src, dest, {:meet, id, who}) do
    "#{who(g, id)} #{meet_name(g, who, run_conf(phase(src, id)), run_conf(phase(dest, id)))}"
  end

  defp meet_name(g, who, _src, _dest) when who in [:ldie, :rdie] do
    "#{side_name(g, side(who))} died"
  end

  defp meet_name(g, who, _src, _dest) when who in [:ldrop, :rdrop] do
    "#{side_name(g, side(who))} dropped"
  end

  defp meet_name(g, who, src, dest) do
    side = side(who)

    if fail_fire?(block_at(g, side, src), dest, side) do
      "#{side_name(g, side)} #{fail_word(g, side, dest)}"
    else
      "#{side_name(g, side)} #{block_show(g, side, src)}"
    end
  end

  defp fail_fire?(%{fail: fail}, dest, side) when is_integer(fail), do: ptr(dest, side) == fail
  defp fail_fire?(_, _, _), do: false

  defp fail_word(g, side, dest) do
    case block_kind(g, side, dest) do
      :stop -> "fail stop"
      :done -> "fail done"
      _ -> "fail"
    end
  end

  defp block_at(g, side, conf) do
    code = if side == :l, do: g.meet.code_l, else: g.meet.code_r

    case ptr(conf, side) do
      :dead -> nil
      i -> Enum.at(code, i)
    end
  end

  defp side(:lside), do: :l
  defp side(:rside), do: :r
  defp side(:ldie), do: :l
  defp side(:rdie), do: :r
  defp side(:ldrop), do: :l
  defp side(:rdrop), do: :r

  defp side_name(g, :l), do: g.meet.name_l
  defp side_name(g, :r), do: g.meet.name_r

  defp block_show(g, side, conf) do
    code = if side == :l, do: g.meet.code_l, else: g.meet.code_r

    case ptr(conf, side) do
      :dead -> "dead"
      i -> show(Enum.at(code, i))
    end
  end

  defp show(%{show: show}), do: show
  defp show(_), do: "?"

  defp run_conf({:run, conf, _, _}), do: conf

  @doc false
  def dump(g, state) do
    Enum.map_join(g.instances, "; ", fn inst ->
      "#{who(g, inst.id)}: #{phase_name(phase(state, inst.id))}"
    end)
  end

  defp who(g, id) do
    inst = Map.fetch!(g.by_id, id)
    "#{inst.key} #{inst.kind} #{inst.index}"
  end

  defp phase_name(:absent), do: "absent"
  defp phase_name(:held), do: "held"
  defp phase_name(:resolved), do: "resolved"
  defp phase_name(:gave_up), do: "gave up"
  defp phase_name({:run, _, 0, _}), do: "running"
  defp phase_name({:run, _, _, _}), do: "retrying"

  defp pp({:not, p}), do: "not #{pp(p)}"
  defp pp({:and, p, q}), do: "#{pp(p)} and #{pp(q)}"
  defp pp({:or, p, q}), do: "#{pp(p)} or #{pp(q)}"
  defp pp({:imp, p, q}), do: "(#{pp(p)}) implies (#{pp(q)})"
  defp pp({atom, key, kind}), do: "#{atom} #{key} #{kind}"
  defp pp(true), do: "true"
  defp pp(false), do: "false"
end
