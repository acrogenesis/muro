defmodule Muro.SynthBudgetTest do
  use ExUnit.Case, async: true

  @queens4 "examples/cshrl/envs/queens4.muro"

  test "the default bounds sit above the 4-queens walk" do
    assert Muro.Synth.considered_budget() == 1_000_000
    assert Muro.Synth.memory_budget() == 512 * 1_048_576
    assert Muro.Synth.considered_budget() > 94_970
  end

  test "a considered budget stops before the next program and names the reason" do
    assert {:empty, "considered budget", meta} =
             Muro.Synth.enumerate_sized(["p", "q"], 4, fn _feature -> 1 end, 2, nil,
               considered_budget: 5
             )

    assert meta.considered == 5
    assert meta.size == 2
    refute Map.has_key?(meta, :bank)
  end

  test "a zero considered budget stops before any program" do
    assert {:empty, "considered budget", meta} =
             Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1, nil,
               considered_budget: 0,
               memory_budget: -1
             )

    assert meta.considered == 0
    assert meta.size == 0
    assert meta.sizes == []
  end

  test "a budget that ends a size names that size" do
    # Size 1 is true, false, and one test per feature: four programs.
    # The budget is that count, so size 2 is not enumerated.
    assert {:empty, "considered budget", meta} =
             Muro.Synth.enumerate_sized(["p", "q"], 4, fn _feature -> 1 end, 2, nil,
               considered_budget: 4
             )

    assert meta.considered == 4
    assert [size, count] = List.last(meta.sizes)
    assert size == 1
    assert count > 0
    assert meta.size == size
    refute Enum.any?(meta.sizes, fn [row, _] -> row > meta.size end)
  end

  test "a finished walk reports the last size that counted a program" do
    assert {:ok, _index, meta} =
             Muro.Synth.enumerate_sized(["p", "q"], 2, fn _feature -> 1 end, 2)

    assert [size, count] = List.last(meta.sizes)
    assert size == 2
    assert count > 0
    assert meta.size == size
    assert meta.considered > 0
    assert meta.distinct > 0
    assert meta.truncated == false
  end

  test "a negative memory budget stops before any candidate" do
    assert {:empty, "memory budget", meta} =
             Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1, nil, memory_budget: -1)

    assert meta.considered == 0
    assert meta.size == 0
    assert meta.sizes == []
  end

  test "a non-integer budget is a usage error" do
    assert {:error, :usage, considered} =
             Muro.Synth.Loop.run("examples/cshrl/envs/two_state.muro", considered_budget: 1.5)

    assert considered =~ "considered budget"

    assert {:error, :usage, memory} =
             Muro.Synth.Loop.run("examples/cshrl/envs/two_state.muro", memory_budget: "512")

    assert memory =~ "memory budget"
  end

  test "enumerate_sized rejects a non-integer budget" do
    assert_raise ArgumentError, ~r/considered_budget must be an integer/, fn ->
      Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1, nil, considered_budget: :no)
    end

    assert_raise ArgumentError, ~r/memory_budget must be an integer/, fn ->
      Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1, nil, memory_budget: 1.0)
    end
  end

  @tag timeout: 180_000
  test "4-queens under a tiny considered budget reports an empty version space" do
    Process.put(:muro_synth_reaches, %{sentinel: true})

    assert {:exit, 1, "", lines} = Muro.CLI.Synth.run([@queens4], considered_budget: 3)
    report = Enum.join(lines, "\n")

    assert report =~ "muro synth: empty version space"
    assert report =~ "considered budget"
    assert report =~ "considered 3"
    refute report =~ "predicate size 18 exhausted"
    refute report =~ "\ndepth 18\n"
    refute report =~ "homomorphism checked"
    refute report =~ "exhausts memory"
    assert Process.get(:muro_synth_reaches) == nil
  end

  @tag timeout: 180_000
  test "--json names a considered-budget stop and the counts the walk reached" do
    assert {:exit, 1, "", [json]} =
             Muro.CLI.Synth.run([@queens4, "--json"], considered_budget: 5)

    decoded = JSON.decode!(json)
    assert decoded["status"] == "empty"
    assert decoded["stop"] == "considered budget"
    assert decoded["considered"] == 5
    assert is_integer(decoded["distinct"])
    assert is_integer(decoded["size"])
    assert [size, _count] = List.last(decoded["sizes"])
    assert decoded["size"] == size
    assert is_integer(decoded["enum_ms"])
    assert is_boolean(decoded["truncated"])
    assert decoded["note"] == "no predicate matches the observations"
  end

  @tag timeout: 180_000
  test "--json names a memory-budget stop and the counts the walk reached" do
    assert {:exit, 1, "", [json]} =
             Muro.CLI.Synth.run([@queens4, "--json"], memory_budget: -1)

    decoded = JSON.decode!(json)
    assert decoded["status"] == "empty"
    assert decoded["stop"] == "memory budget"
    assert decoded["considered"] == 0
    assert decoded["size"] == 0
    assert decoded["sizes"] == []
    assert is_integer(decoded["enum_ms"])
  end

  test "a failed run clears the search memo" do
    Process.put(:muro_synth_reaches, %{sentinel: true})

    assert {:error, :book, _message} =
             Muro.Synth.Loop.run("/no/such/queens-review-fix.muro")

    assert Process.get(:muro_synth_reaches) == nil
  end

  test "a finished run clears the search memo" do
    Process.put(:muro_synth_reaches, %{sentinel: true})

    assert {:ok, result} =
             Muro.Synth.Loop.run("examples/cshrl/envs/two_state.muro",
               depth: 0,
               max_depth: 0
             )

    assert result.status == :certified
    assert Process.get(:muro_synth_reaches) == nil
    refute Map.has_key?(result, :considered)
  end
end
