defmodule Muro.FillTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  @add1 "examples/fill/add1.muro"
  @golden "examples/fill/add1.filled.muro"

  test "mix muro.fill writes the successor and the book checks" do
    dir = tmp_dir()
    path = Path.join(dir, "add1.muro")
    File.cp!(@add1, path)

    out =
      capture_io(fn ->
        assert Mix.Tasks.Muro.Fill.run([path, "--def", "add1"]) == :ok
      end)

    assert out =~ "filled add1\n"
    assert File.read!(path) == File.read!(@golden)
    assert Muro.check_file(path) == :ok
  end

  test "closed equations reject a type-correct constant and the identity" do
    dir = tmp_dir()
    path = Path.join(dir, "add1.muro")
    before = File.read!(@add1)
    File.write!(path, before)

    assert_raise Mix.Error,
                 ~r/bound 2 reached: tried 2 candidates, 2 type-checked but failed the closed equations/,
                 fn ->
                   Mix.Tasks.Muro.Fill.run([path, "--def", "add1", "--bound", "2"])
                 end

    assert File.read!(path) == before
    refute Enum.any?(File.ls!(dir), &String.contains?(&1, ".muro-fill-"))
  end

  test "identity equations fill the bound variable" do
    src = """
    def idn : run Π (n : Nat) → Nat :=
      ?

    def idn-0 : evidence {idn 0 ≡ 0 : Nat} :=
      refl

    def idn-1 : evidence {idn suc(0) ≡ suc(0) : Nat} :=
      refl
    """

    dir = tmp_dir()
    path = Path.join(dir, "idn.muro")
    File.write!(path, src)

    capture_io(fn ->
      assert Mix.Tasks.Muro.Fill.run([path, "--def", "idn"]) == :ok
    end)

    assert File.read!(path) == String.replace(src, "?", "λ (n : Nat) → n")
    assert Muro.check_file(path) == :ok
  end

  test "evidence is filled from its type" do
    src = """
    def unit_ok : evidence {0 ≡ 0 : Nat} :=
      ?
    """

    dir = tmp_dir()
    path = Path.join(dir, "unit_ok.muro")
    File.write!(path, src)

    capture_io(fn ->
      assert Mix.Tasks.Muro.Fill.run([path, "--def", "unit_ok"]) == :ok
    end)

    assert File.read!(path) == String.replace(src, "?", "refl")
    assert Muro.check_file(path) == :ok
  end

  test "the same book and bound produce the same body" do
    dir = tmp_dir()
    left = Path.join(dir, "left.muro")
    right = Path.join(dir, "right.muro")
    File.cp!(@add1, left)
    File.cp!(@add1, right)

    capture_io(fn ->
      assert Mix.Tasks.Muro.Fill.run([left, "--def", "add1", "--bound", "8"]) == :ok
      assert Mix.Tasks.Muro.Fill.run([right, "--def", "add1", "--bound", "8"]) == :ok
    end)

    assert File.read!(left) == File.read!(right)
    assert File.read!(left) == File.read!(@golden)
  end

  test "a candidate does not call the definition being filled" do
    src = File.read!(@add1)
    assert {:ok, terms} = Muro.Fill.candidates(src, "add1", 5)

    assert Enum.take(terms, 2) == [
             {:lam, :affine, :nat, "n", :ze},
             {:lam, :affine, :nat, "n", {:var, "n"}}
           ]

    refute Enum.any?(terms, &Muro.Fill.refers?(&1, "add1"))
    assert Enum.any?(terms, &match?({:lam, _, _, _, {:mnat, _, _, _, _, _, _}}, &1))
    assert length(terms) == 60
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_fill_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
