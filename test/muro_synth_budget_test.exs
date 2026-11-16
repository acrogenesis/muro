defmodule Muro.SynthBudgetTest do
  # The considered and memory bounds are process-wide. This module is
  # synchronous so an override cannot race another file's enumeration.
  use ExUnit.Case, async: false

  @queens4 "examples/cshrl/envs/queens4.muro"

  setup do
    considered = Application.get_env(:muro, :synth_considered_budget)
    memory = Application.get_env(:muro, :synth_memory_budget)

    on_exit(fn ->
      restore(:synth_considered_budget, considered)
      restore(:synth_memory_budget, memory)
    end)

    :ok
  end

  test "the default bounds sit above the 4-queens walk" do
    Application.delete_env(:muro, :synth_considered_budget)
    Application.delete_env(:muro, :synth_memory_budget)

    assert Muro.Synth.considered_budget() == 1_000_000
    assert Muro.Synth.memory_budget() == 512 * 1_048_576
    assert Muro.Synth.considered_budget() > 94_970
  end

  test "a considered budget stops before the next program and names the reason" do
    Application.put_env(:muro, :synth_considered_budget, 5)
    Application.delete_env(:muro, :synth_memory_budget)

    assert {:empty, "considered budget", meta} =
             Muro.Synth.enumerate_sized(["p", "q"], 4, fn _feature -> 1 end, 2)

    assert meta.considered == 5
    refute Map.has_key?(meta, :bank)
  end

  test "a zero considered budget stops before any program" do
    Application.put_env(:muro, :synth_considered_budget, 0)
    Application.put_env(:muro, :synth_memory_budget, -1)

    assert {:empty, "considered budget", meta} =
             Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1)

    assert meta.considered == 0
  end

  test "a negative memory budget stops at the first program" do
    Application.delete_env(:muro, :synth_considered_budget)
    Application.put_env(:muro, :synth_memory_budget, -1)

    assert {:empty, "memory budget", meta} =
             Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1)

    assert meta.considered == 0
  end

  @tag timeout: 180_000
  test "4-queens under a tiny considered budget reports an empty version space" do
    Application.put_env(:muro, :synth_considered_budget, 3)
    Application.delete_env(:muro, :synth_memory_budget)
    Process.put(:muro_synth_reaches, %{sentinel: true})

    assert {:exit, 1, "", lines} = Muro.CLI.Synth.run([@queens4])
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

  defp restore(key, nil), do: Application.delete_env(:muro, key)
  defp restore(key, value), do: Application.put_env(:muro, key, value)
end
