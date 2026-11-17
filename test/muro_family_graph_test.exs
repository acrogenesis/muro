defmodule Muro.Family.GraphTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Parser}
  alias Muro.Family.Graph

  @trace "always ((opened a signal) implies (resolved a init)) fails in slots after a init 0 opens, a signal 1 opens: a init 0: running; a signal 1: running; b init 0: absent"

  @formula {:forall, "k", {:dat, "key", []},
            {:always, {:imp, {:opened, "k", "signal"}, {:resolved, "k", "init"}}}}

  test "no-overtake holds, and the same book with the signal unheld is refused" do
    src = File.read!("examples/keyed-slots.muro")
    {:ok, search} = prepare(src)
    assert Graph.decide(search, @formula) == {:ok, 171_649, 729_184}
    assert Enum.all?(search.states, &Graph.respects?(search.g, &1))

    g = search.g
    late = Enum.find(search.states, &late_init?/1)
    assert late
    assert Graph.holds?(g, {:imp, {:opened, "a", "signal"}, {:resolved, "a", "init"}}, late)

    assert Enum.any?(search.states, fn state ->
             Graph.phase(state, 0) == :gave_up and running?(Graph.phase(state, 1)) and
               Graph.known_at_open?(state, 1, 0)
           end)

    assert Enum.any?(search.states, fn state ->
             match?({:run, _, n, _}, Graph.phase(state, 0)) and
               elem(Graph.phase(state, 0), 2) > 0 and Graph.phase(state, 1) == :held
           end)

    assert Enum.any?(search.states, fn state ->
             running?(Graph.phase(state, 1)) and Graph.phase(state, 0) == :absent
           end)

    assert Enum.any?(search.states, fn state ->
             running?(Graph.phase(state, 1)) and Graph.phase(state, 2) == :held
           end)

    refute Enum.any?(search.states, fn state ->
             running?(Graph.phase(state, 2)) and
               (running?(Graph.phase(state, 1)) or Graph.phase(state, 1) == :held) and
               Graph.known_at_open?(state, 2, 1)
           end)

    assert Graph.decide(search, {:always, false}) ==
             {:error,
              "always (false) fails in slots: a init 0: absent; a signal 1: absent; a signal 2: absent; b init 0: absent"}

    assert Graph.decide(search, {:eventually, true}) == {:error, "not yet decided"}

    never = String.replace(src, "signal held while earlier unresolved", "signal never held")
    assert {:error, msg} = check(never)
    assert msg =~ @trace
    refute msg =~ "resolves"
    refute msg =~ "not yet decided"
  end

  test "a second init opens at once and a later signal waits for both" do
    src = File.read!("examples/keyed-slots.muro")
    {:ok, book} = Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))

    instances = [
      %{id: 0, key: "a", kind: "init", index: 0},
      %{id: 1, key: "a", kind: "init", index: 1},
      %{id: 2, key: "a", kind: "signal", index: 2}
    ]

    assert {:ok, search} = Graph.prepare(book, family, instances: instances)
    g = search.g

    assert Enum.any?(search.states, fn state ->
             running?(Graph.phase(state, 0)) and running?(Graph.phase(state, 1))
           end)

    assert Enum.any?(search.states, fn state ->
             running?(Graph.phase(state, 0)) and running?(Graph.phase(state, 1)) and
               Graph.phase(state, 2) == :held
           end)

    assert Enum.any?(search.states, fn state ->
             running?(Graph.phase(state, 2)) and Graph.phase(state, 0) == :absent and
               Graph.phase(state, 1) == :absent
           end)

    refute Enum.any?(search.states, fn state ->
             running?(Graph.phase(state, 2)) and Graph.known_at_open?(state, 2, 0) and
               unresolved_init?(Graph.phase(state, 0))
           end)

    assert Graph.respects?(g, hd(search.states))
    assert Enum.all?(search.states, &Graph.respects?(g, &1))
  end

  test "a server that stops stays unresolved and the signal stays held" do
    src = """
    data Event : Type where
      init : Event
      signal : Event
    data Report : Type where
      ok : Report
    session task-work := send Report end
    session server-wait := recv Report end
    conform task : task-work := put ok done
    conform server : server-wait :=
      get (r : Report) done
      fail
        stop
    meet slot : server with task may fail buffer 1
    family slots : slot per key of Event
      init never held
      signal held while earlier unresolved
    """

    {:ok, book} = Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))

    instances = [
      %{id: 0, key: "a", kind: "init", index: 0},
      %{id: 1, key: "a", kind: "signal", index: 1}
    ]

    assert {:ok, search} = Graph.prepare(book, family, instances: instances)

    assert Enum.any?(search.states, fn state ->
             Graph.phase(state, 1) == :held and running?(Graph.phase(state, 0)) and
               Graph.edges(search.g, state) == [{:stay, state}]
           end)
  end

  test "two always formulas share one family graph" do
    src = """
    data Event : Type where
      init : Event
    session ping := send Nat end
    session pong := recv Nat end
    conform a : ping := put 0 done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    family slots : wire per key of Event
      init never held
    temporal one : slots := forall (k : key). always true
    temporal two : slots := forall (k : key). always true
    """

    assert check(src) == :ok
    assert ["family slots: wire per key of Event", one, two] = Check.temporal_lines()
    assert one =~ ~r/^temporal one: holds in (\d+) reachable states, (\d+) transitions$/
    assert two =~ ~r/^temporal two: holds in (\d+) reachable states, (\d+) transitions$/
    assert counts(one) == counts(two)
  end

  test "decide refuses a quantifier that is not a key" do
    search = %{
      g: %{keys: ["a"], family: "slots", instances: []},
      states: [],
      parents: %{},
      transitions: 0
    }

    assert Graph.decide(search, {:forall, "c", :bit, {:always, true}}) ==
             {:error, "forall over Bit is not a key"}

    assert Graph.decide(search, {:forall, "c", {:dat, "Event", []}, {:always, true}}) ==
             {:error, "forall over Event is not a key"}

    assert Graph.decide(search, {:forall, "c", :bit, {:eventually, true}}) ==
             {:error, "forall over Bit is not a key"}
  end

  test "prepare refuses a stuck meeting before the family search" do
    src = """
    data Event : Type where
      init : Event
    session ping := recv Nat end
    session pong := recv Nat end
    conform a : ping := get (n : Nat) done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    family slots : wire per key of Event
      init never held
    """

    {:ok, book} = Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))
    assert {:error, msg} = Graph.prepare(book, family)
    assert msg =~ "deadlock"
  end

  test "always false fails at the start" do
    src = """
    data Event : Type where
      init : Event
    session ping := send Nat end
    session pong := recv Nat end
    conform a : ping := put 0 done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    family slots : wire per key of Event
      init never held
    temporal no : slots := always false
    """

    assert {:error, msg} = check(src)
    assert msg =~ "no: always (false) fails in slots: a init 0: absent; b init 0: absent"
  end

  test "a vector payload is outside the fragment" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               init : Event
             session out (k : Nat) := send (Vec Nat k) (recv (Vec Nat k) end)
             session out1 := out 1
             conform vec-a : out1 := put (rep 1 0) (get (v : Vec Nat 1) done)
             conform vec-b : out1 := put (rep 1 0) (get (v : Vec Nat 1) done)
             meet vec-wire : vec-a with vec-b buffer 1
             family slots : vec-wire per key of Event
               init never held
             temporal t : slots := always true
             """)

    assert msg =~ "t: payload outside the temporal fragment"
    refute msg =~ "not yet decided"
  end

  defp prepare(src) do
    {:ok, book} = Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))
    Graph.prepare(book, family)
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end

  defp counts(line) do
    [_, n, m] = Regex.run(~r/holds in (\d+) reachable states, (\d+) transitions/, line)
    {n, m}
  end

  defp running?({:run, _, _, _}), do: true
  defp running?(_), do: false

  defp unresolved_init?({:run, _, _, _}), do: true
  defp unresolved_init?(:held), do: true
  defp unresolved_init?(_), do: false

  defp late_init?(state) do
    running?(Graph.phase(state, 1)) and running?(Graph.phase(state, 0)) and
      not Graph.known_at_open?(state, 1, 0)
  end
end
