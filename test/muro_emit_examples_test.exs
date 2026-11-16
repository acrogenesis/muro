defmodule Muro.EmitExamplesTest do
  use ExUnit.Case, async: false

  Code.require_file("emit_examples.exs", __DIR__)

  # A previous test in this process can leave checker state behind.
  # The picture is the one a fresh process emits. The walk is the
  # whole examples tree, so the cap sits above the module default.
  @tag timeout: 180_000
  test "every example that existed before the family emits the same image" do
    got =
      fn -> Muro.EmitExamples.lines() end
      |> Task.async()
      |> Task.await(:infinity)

    expected =
      "test/fixtures/emit-examples.digest"
      |> File.read!()
      |> String.trim_trailing()
      |> String.split("\n")

    assert got == expected
  end
end
